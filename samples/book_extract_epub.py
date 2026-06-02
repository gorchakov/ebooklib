"""
Book Extract Utility

Extracts sections from an EPUB book and creates new EPUBs with proper TOC.
Preserves hierarchical structure for sections with subsections.
Uses ebooklib for EPUB manipulation.

Usage:
    from backend.utils.book_extract_epub import BookExtractorEPUB
    
    extractor = BookExtractorEPUB('/path/to/book.epub')
    
    # Analyze book structure
    sections = extractor.analyze()
    
    # Extract a single section (with subsections if present)
    section = sections[0]
    new_epub_bytes = extractor.create_epub_from_section(section, new_title='Custom Title')
    
    # Or split into multiple books using hrefs
    section_hrefs = ['text/chapter1.xhtml', 'text/chapter2.xhtml']
    results = extractor.split(section_hrefs, cover_replacements={})
    for title, epub_bytes, cover_base64 in results:
        # Save each book
        pass
"""

import io
import base64
import os
import shutil
import tempfile
import zipfile
from typing import Optional, Dict, List, Tuple
from pathlib import Path
import ebooklib
from ebooklib import epub
import re
from ebooklib.epub import EpubReader, EpubBook
import traceback
from epubcheck import EpubCheck
from lxml import html
from PIL import Image

CONTAINER_NS = {"c": "urn:oasis:names:tc:opendocument:xmlns:container"}
OPF_NS = {"opf": "http://www.idpf.org/2007/opf"}
EPUB_NS = "http://www.idpf.org/2007/ops"
XHTML_NS = "http://www.w3.org/1999/xhtml"

PREFIX_PAIR_RE = re.compile(r"([A-Za-z][\w\-.]*):\s*([^\s]+)")

class ReaderWithPrefixes(EpubReader):
    def load(self) -> EpubBook:
        super(ReaderWithPrefixes, self).load()   # builds self.container and self.book
        pkg = self.container.getroot()           # <package>
        pref = pkg.get("prefix") or ""
        self.book.prefixes.extend(f"{m.group(1)}: {m.group(2)}" for m in PREFIX_PAIR_RE.finditer(pref))
        return self.book

def read_epub_with_prefixes(path, options=None) -> EpubBook:
    r = ReaderWithPrefixes(path, options)
    book = r.load()
    r.process()
    return book

def copy_prefixes(src_book, dst_book):
    seen = set()
    for entry in getattr(src_book, "prefixes", []):
        if not entry or ":" not in entry:
            continue
        name, uri = entry.split(":", 1)
        name, uri = name.strip(), uri.strip()
        key = (name, uri)
        if key in seen:
            continue
        seen.add(key)
        dst_book.add_prefix(name, uri)


class BookExtractorEPUB:
    """
    Extracts a specific section from an EPUB book and creates a new EPUB.
    """
    
    # Skip these common sections (case-insensitive)
    SKIP_SECTIONS = {
        'titlepage', 'title page',
        'imprint',
        'colophon',
        'copyright',
        'uncopyright',
        'dedication',
        'acknowledgments', 'acknowledgements',
        'about the author', 'about the publisher',
        'table of contents', 'contents',
        'frontmatter', 'front matter',
        'endmatter', 'end matter',
        'cover'
    }
    
    def __init__(self, epub_path: str):
        """
        Initialize extractor with EPUB file path.
        
        Args:
            epub_path: Path to EPUB file
        """
        self.epub_path = Path(epub_path)

        # Read EPUB using ebooklib
        try:
            self.book = read_epub_with_prefixes(str(self.epub_path))
        except Exception as e:
            raise FileNotFoundError(f"EPUB file not found: {epub_path}: {e}")
        
        # Lazy-loaded caches
        self._extracted_metadata = None
        self._extracted_styles = None
        self._extracted_images = None
        self._cover_image = None
        
        # Lazy-loaded item lookup indices
        self._items_by_href = None
        self._items_by_name = None
        self._document_items = None
    
    def _build_item_indices(self):
        """Build lookup indices for fast item retrieval."""
        if self._items_by_href is not None:
            return  # Already built
        
        self._items_by_href = {}
        self._items_by_name = {}
        self._document_items = []
        
        for item in self.book.get_items_of_type(ebooklib.ITEM_DOCUMENT):
            self._document_items.append(item)
            
            # Index by file_name (href)
            if hasattr(item, 'file_name') and item.file_name:
                self._items_by_href[item.file_name] = item
            
            # Index by get_name()
            if hasattr(item, 'get_name'):
                name = item.get_name()
                self._items_by_name[name] = item
    
    def _extract_metadata(self) -> Dict:
        """Extract metadata from the original book."""
        if self._extracted_metadata is not None:
            return self._extracted_metadata
        
        metadata = {}
        
        # Extract identifier
        identifier_meta = self.book.get_metadata('DC', 'identifier')
        if identifier_meta:
            metadata['identifier'] = identifier_meta[0][0]
        else:
            metadata['identifier'] = None
        
        # Extract title
        title_meta = self.book.get_metadata('DC', 'title')
        if title_meta:
            metadata['title'] = title_meta[0][0]
        else:
            metadata['title'] = None
        
        # Extract language
        language_meta = self.book.get_metadata('DC', 'language')
        if language_meta:
            metadata['language'] = language_meta[0][0]
        else:
            metadata['language'] = 'en'  # Default to English
        
        # Extract description (if available)
        description_meta = self.book.get_metadata('DC', 'description')
        if description_meta:
            metadata['description'] = description_meta[0][0]
        else:
            metadata['description'] = None
        
        # Extract rights (if available)
        rights_meta = self.book.get_metadata('DC', 'rights')
        if rights_meta:
            metadata['rights'] = rights_meta[0][0]
        else:
            metadata['rights'] = None
        
        # Extract authors
        creators = self.book.get_metadata('DC', 'creator')
        metadata['authors'] = [creator[0] for creator in creators] if creators else []
        
        # Extract publisher
        publisher_meta = self.book.get_metadata('DC', 'publisher')
        if publisher_meta:
            metadata['publisher'] = publisher_meta[0][0]
        else:
            metadata['publisher'] = None
        
        # Extract date
        date_meta = self.book.get_metadata('DC', 'date')
        if date_meta:
            metadata['date'] = date_meta[0][0]
        else:
            metadata['date'] = None
        
        self._extracted_metadata = metadata
        return metadata
    
    def _extract_styles(self) -> List:
        """Extract all style items (CSS) from the book."""
        if self._extracted_styles is not None:
            return self._extracted_styles
        
        styles = []
        for item in self.book.get_items_of_type(ebooklib.ITEM_STYLE):
            styles.append(item)
        
        self._extracted_styles = styles
        return styles
    
    def _extract_images(self) -> List:
        """Extract all image items from the book."""
        if self._extracted_images is not None:
            return self._extracted_images
        
        images = []
        for item in self.book.get_items_of_type(ebooklib.ITEM_IMAGE):
            images.append(item)
        
        self._extracted_images = images
        return images
    
    def _extract_cover(self) -> Optional[bytes]:
        """Extract cover image from the book."""
        if self._cover_image is not None:
            return self._cover_image
        
        # Try to get cover image
        cover_item = next(self.book.get_items_of_type(ebooklib.ITEM_COVER), None)
        if cover_item:
            self._cover_image = cover_item.get_content()
        else:
            self._cover_image = None
        
        return self._cover_image
    
    def get_metadata(self) -> Dict:
        """Get extracted metadata."""
        if self._extracted_metadata is None:
            self._extract_metadata()
        return self._extracted_metadata.copy()
    
    def get_cover_image(self) -> Optional[str]:
        """Get cover image as base64 string."""
        if self._cover_image is None:
            self._extract_cover()
        if self._cover_image:
            return base64.b64encode(self._cover_image).decode('utf-8')
        return None
    
    def get_book_metadata(self) -> Dict[str, Optional[str]]:
        """
        Extract metadata from the original book (alias for get_metadata for compatibility).
        
        Returns:
            Dict with keys: title, author, description, language
        """
        metadata = self.get_metadata()
        return {
            'title': metadata.get('title'),
            'author': metadata.get('authors', [None])[0] if metadata.get('authors') else None,
            'description': metadata.get('description'),
            'language': metadata.get('language')
        }
    
    def _should_skip_section(self, title: str) -> bool:
        """Check if section should be skipped based on title."""
        title_lower = title.lower().strip()
        return title_lower in self.SKIP_SECTIONS
    
    def _normalize_string(self, value: any) -> Optional[str]:
        """
        Normalize a string value, handling None, empty strings, and whitespace.
        
        Args:
            value: String value to normalize
            
        Returns:
            Normalized string or None if value is empty/invalid
        """
        if not value:
            return None
        if not isinstance(value, str):
            return None
        normalized = value.strip()
        return normalized if normalized else None
    
    def _parse_toc_link(self, link_item) -> Optional[Dict[str, any]]:
        """
        Parse a TOC link item (epub.Link, epub.Section, or tuple) into a section dict.
        
        Args:
            link_item: Can be:
                - epub.Link object
                - epub.Section object  
                - tuple: (title, href) or (title, href, uid, [children])
                - tuple: (epub.Section, [children]) - Section with nested children
        
        Returns:
            Section dict with 'title', 'href', 'children', 'recommended' or None
        """
        title = None
        href = None
        children = []
        
        # Handle epub.Section objects directly
        if isinstance(link_item, epub.Section):
            title = getattr(link_item, 'title', None)
            href = getattr(link_item, 'href', None)
            # Sections may have children
            if hasattr(link_item, 'children') and link_item.children:
                for child in link_item.children:
                    child_section = self._parse_toc_link(child)
                    if child_section:
                        children.append(child_section)
        
        # Handle epub.Link objects
        elif isinstance(link_item, epub.Link):
            title = getattr(link_item, 'title', None)
            href = getattr(link_item, 'href', None)
            # Check for children (epub.Link might have children as a list)
            if hasattr(link_item, 'children') and link_item.children:
                for child in link_item.children:
                    child_section = self._parse_toc_link(child)
                    if child_section:
                        children.append(child_section)
        
        # Handle tuples: multiple formats possible
        elif isinstance(link_item, tuple):
            if len(link_item) >= 2:
                first_elem = link_item[0]
                second_elem = link_item[1]
                
                # Pattern 1: (epub.Section, [children]) - Section with nested children
                # This is the pattern shown in the screenshots
                if isinstance(first_elem, epub.Section):
                    title = getattr(first_elem, 'title', None)
                    href = getattr(first_elem, 'href', None)
                    # Second element is a list of children
                    if isinstance(second_elem, list):
                        for child in second_elem:
                            child_section = self._parse_toc_link(child)
                            if child_section:
                                children.append(child_section)
                
                # Pattern 2: (title, href) or (title, href, uid) or (title, href, uid, [children])
                # Legacy tuple format for backward compatibility
                elif isinstance(first_elem, str):
                    title = first_elem if first_elem else None
                    href = second_elem if isinstance(second_elem, str) else None
                    # Check for nested children (4th element)
                    if len(link_item) > 3 and link_item[3]:
                        children_list = link_item[3]
                        if isinstance(children_list, list):
                            for child in children_list:
                                child_section = self._parse_toc_link(child)
                                if child_section:
                                    children.append(child_section)
        else:
            return None
        
        # Normalize title and href (handle empty strings, None, etc.)
        title = self._normalize_string(title)
        href = self._normalize_string(href)
        
        # If title or href is missing but we have children, try to get from first child
        # This handles cases where a section element has no direct title/href but contains nested elements.
        # This is common in ebooklib's TOC structure where parent sections may not have explicit titles
        # but their first child does (similar to how book_splitter_epub.py extracts text from nested <a> tags).
        if children:
            first_child = children[0]
            if first_child:
                child_title = self._normalize_string(first_child.get('title'))
                child_href = self._normalize_string(first_child.get('href'))
                if not title and child_title:
                    title = child_title
                if not href and child_href:
                    href = child_href
        
        # If we still don't have both title and href, we can't create a valid section
        if not title or not href:
            return None
        
        # Keep fragment identifier in href - it's needed for subsection navigation
        # (e.g., text/chapter.xhtml#section-1 points to anchor within the file)
        
        # Determine if this should be recommended for extraction
        recommended = not self._should_skip_section(title)
        
        return {
            'title': title,  # Already normalized
            'href': href,    # Already normalized
            'children': children,
            'recommended': recommended
        }
    
    def analyze(self) -> List[Dict[str, any]]:
        """
        Analyze EPUB and return list of sections that can be extracted.
        
        Returns:
            List of sections with metadata:
            [
                {
                    'title': 'Section Title',
                    'href': 'text/section.xhtml',
                    'children': [...],  # Nested sections
                    'recommended': True/False  # Whether to include by default
                },
                ...
            ]
        """
        if not hasattr(self.book, 'toc') or not self.book.toc:
            # Build indices if not already built
            self._build_item_indices()
            
            # Fallback: try to build sections from all document items
            sections = []
            for item in self._document_items:
                title = self._get_section_title(item)
                file_name = item.file_name if hasattr(item, 'file_name') else item.get_name()
                
                # Skip nav and ncx files
                if 'nav' in file_name.lower() or 'ncx' in file_name.lower():
                    continue
                
                section = {
                    'title': title,
                    'href': file_name,
                    'children': [],
                    'recommended': not self._should_skip_section(title)
                }
                sections.append(section)
            
            return sections
        
        sections = []
        # Parse TOC structure
        for toc_item in self.book.toc:
            section = self._parse_toc_link(toc_item)
            if section:
                sections.append(section)
        
        return sections
    
    def _get_items_for_section(self, section: Dict[str, any]) -> List[epub.EpubHtml]:
        """
        Get all EpubHtml items that belong to a section.
        
        Args:
            section: Section dictionary with 'href' and 'children'
        
        Returns:
            List of EpubHtml items
        """
        items = []
        
        # Find item by href
        href = section.get('href', '')
        if href:
            item = self.find_item_by_href(href)
            if item and item not in items:
                items.append(item)
        
        # Add child section items recursively
        for child in section.get('children', []):
            child_items = self._get_items_for_section(child)
            for item in child_items:
                if item not in items:
                    items.append(item)
        
        return items
    
    def estimate_section_pages(self, section: Dict[str, any], words_per_page: int = 250) -> int:
        """
        Estimate number of pages for a specific section.
        
        Args:
            section: Section dictionary with 'href' and 'children'
            words_per_page: Average words per page (default 250 for standard paperback)
        
        Returns:
            Estimated page count (minimum 1 if section has content, 0 if no content)
        """
        items = self._get_items_for_section(section)
        if not items:
            return 0
        
        word_count = 0
        for item in items:
            try:
                content = item.get_content()
                tree = html.fromstring(content)
                
                # Extract text from body
                body = tree.find('.//body')
                if body is None:
                    body = tree
                
                # Recursively extract text and count words
                for elem in body.iter():
                    # Skip script and style tags
                    if hasattr(elem, 'tag') and isinstance(elem.tag, str):
                        tag_name = elem.tag.lower().split('}')[-1]  # Remove namespace
                        if tag_name in ['script', 'style', 'code', 'pre']:
                            continue
                    
                    if hasattr(elem, 'text') and elem.text and elem.text.strip():
                        word_count += len(elem.text.split())
                    
                    if hasattr(elem, 'tail') and elem.tail and elem.tail.strip():
                        word_count += len(elem.tail.split())
            
            except Exception:
                continue
        
        if word_count == 0:
            return 0
        return max(1, round(word_count / words_per_page))
    
    def _find_section_by_href(self, sections: List[Dict[str, any]], href: str) -> Optional[Dict[str, any]]:
        """
        Find a section by href in the analyzed section tree (recursive search).
        
        Args:
            sections: List of section dicts to search
            href: Href to search for (e.g., 'text/chapter.xhtml')
            
        Returns:
            Section dict if found, None otherwise
        """
        # Normalize hrefs for comparison (remove fragments)
        search_href = href.split('#')[0]
        
        for section in sections:
            section_href = section.get('href', '').split('#')[0]
            if section_href == search_href:
                return section
            
            # Search in children recursively
            children = section.get('children', [])
            if children:
                result = self._find_section_by_href(children, href)
                if result:
                    return result
        
        return None
    
    def split(self, section_hrefs: List[str]) -> List[Tuple[str, bytes]]:
        """
        Split EPUB into separate books for each section.
        
        Args:
            section_hrefs: List of section hrefs to extract (e.g., ['text/chapter1.xhtml', ...])
        Returns:
            List of tuples: (section_title, epub_bytes, cover_base64)
        """

        
        # Analyze book to get fresh section structure from the file
        all_sections = self.analyze()

        results = []
        
        for href in section_hrefs:
            # Find the section in analyzed structure by href
            section = self._find_section_by_href(all_sections, href)
            
            if not section:
                print(f"Warning: Section not found for href '{href}'")
                continue
            
            title = section.get('title', 'Untitled Section')
            
            # Extract the section with all subsections and proper TOC
            try:
                epub_bytes = self.create_epub_from_section(section, new_title=title)
                results.append((title, epub_bytes))
            except Exception as e:
                print(f"Warning: Failed to extract section '{title}': {e}")                
                traceback.print_exc()
                continue
        
        return results
    
   
    def find_item_by_href(self, href: str) -> Optional[epub.EpubHtml]:
        """
        Find a document item by its href/file_name.
        
        Args:
            href: Href or file_name to search for
            
        Returns:
            EpubHtml item if found, None otherwise
        """
        # Build indices if not already built
        self._build_item_indices()
        
        # Try exact match first (most common case)
        if href in self._items_by_href:
            return self._items_by_href[href]
        if href in self._items_by_name:
            return self._items_by_name[href]
        
        # Fallback to partial matching (for backward compatibility)
        for file_name, item in self._items_by_href.items():
            if href in file_name or file_name.endswith(href):
                return item
        
        for name, item in self._items_by_name.items():
            if href in name or name.endswith(href):
                return item
        
        return None
    
    def _get_section_title(self, item: epub.EpubHtml) -> str:
        """
        Get title from section item.
        
        Args:
            item: EpubHtml item
            
        Returns:
            Title string
        """
        # Use item.title if available
        if hasattr(item, 'title') and item.title:
            return item.title
        
        # Fallback to file name
        if hasattr(item, 'file_name'):
            return Path(item.file_name).stem
        
        return "Extracted Section"
    
    def _collect_dependencies(self, item: epub.EpubHtml) -> Tuple[List, List]:
        """
        Collect all dependencies (images, styles) referenced by the item.
        
        Args:
            item: EpubHtml item
            
        Returns:
            Tuple of (images_list, styles_list)
        """
        images = []
        styles = []
        
        # Lazy load images and styles if needed
        if self._extracted_images is None:
            self._extract_images()
        if self._extracted_styles is None:
            self._extract_styles()
        
        try:
            content = item.get_content()
            tree = html.fromstring(content)
            
            # Find all image references
            for img in tree.xpath('.//img'):
                src = img.get('src', '')
                if src:
                    # Remove fragment and query params
                    src = src.split('#')[0].split('?')[0]
                    # Find matching image item
                    for img_item in self._extracted_images:
                        if src in img_item.get_name() or img_item.get_name().endswith(src):
                            if img_item not in images:
                                images.append(img_item)
                            break
            
            # Find all CSS references
            for link in tree.xpath('.//link[@rel="stylesheet"]'):
                href = link.get('href', '')
                if href:
                    href = href.split('#')[0].split('?')[0]
                    # Find matching style item
                    for style_item in self._extracted_styles:
                        if href in style_item.get_name() or href.endswith(style_item.get_name()):
                            if style_item not in styles:
                                styles.append(style_item)
                            break
                
        except Exception as e:
            print(f"Warning: Error collecting dependencies: {e}")
        
        return images, styles
    
    def _validate_epub(self, epub_path: str, context: str = ""):
        """
        Validate EPUB file using EpubCheck and log results to stdout.
        
        Args:
            epub_path: Path to the EPUB file to validate
            context: Optional context string (e.g., "extraction", "split")
        """
        try:
            # Run EpubCheck
            result = EpubCheck(epub_path, autorun=True)
            
            # Prepare log message
            status = "✓ VALID" if result.valid else "✗ INVALID"
            log_prefix = f"[EPUB-VALIDATION] {context}" if context else "[EPUB-VALIDATION]"
            
            # Log summary
            print(f"{log_prefix} {status} - {epub_path}")
            print(f"{log_prefix} Checker: {result.checker.checkerVersion}")
            print(f"{log_prefix} Errors: {result.checker.nError}, Warnings: {result.checker.nWarning}, Fatal: {result.checker.nFatal}")
            
            # Log all messages (errors, warnings, etc.)
            if result.messages:
                print(f"{log_prefix} Messages ({len(result.messages)} total):")
                for msg in result.messages:
                    print(f"{log_prefix}   [{msg.level}] {msg.id} - {msg.message}")
                    print(f"{log_prefix}     Location: {msg.location}")
                    if msg.suggestion:
                        print(f"{log_prefix}     Suggestion: {msg.suggestion}")
            else:
                print(f"{log_prefix} No validation messages.")
                
        except Exception as e:
            print(f"[EPUB-VALIDATION] ERROR: Failed to validate {epub_path}: {e}")
    
    def _find_toc_entry_by_href(self, toc_items, target_href: str) -> Optional[any]:
        """
        Find a TOC entry in the original book's TOC by matching href.
        
        Args:
            toc_items: TOC items from self.book.toc (list of Link/Section/tuples)
            target_href: Href to search for (without fragment)
            
        Returns:
            TOC entry (Link, Section, or tuple) if found, None otherwise
        """
        # Normalize target href (remove fragment)
        target_href_base = target_href.split('#')[0]
        
        for toc_item in toc_items:
            # Handle different TOC item types
            if isinstance(toc_item, tuple):
                # Could be (Section, [children]) or (title, href, ...)
                first_elem = toc_item[0]
                if isinstance(first_elem, epub.Section):
                    section_href = getattr(first_elem, 'href', '')
                    if section_href and section_href.split('#')[0] == target_href_base:
                        return toc_item
                    # Search in children
                    if len(toc_item) > 1 and isinstance(toc_item[1], list):
                        result = self._find_toc_entry_by_href(toc_item[1], target_href)
                        if result:
                            return result
            elif isinstance(toc_item, (epub.Link, epub.Section)):
                item_href = getattr(toc_item, 'href', '')
                if item_href and item_href.split('#')[0] == target_href_base:
                    return toc_item
                # Check children if present
                if hasattr(toc_item, 'children') and toc_item.children:
                    result = self._find_toc_entry_by_href(toc_item.children, target_href)
                    if result:
                        return result
        
        return None
    
    def _build_toc_from_original(self, toc_entry: any, new_file_name: str) -> any:
        """
        Build TOC structure from original book's TOC entry, remapping hrefs to new file.
        
        Args:
            toc_entry: Original TOC entry (Link, Section, or tuple) from self.book.toc
            new_file_name: The new filename for the extracted content
            
        Returns:
            New TOC entry with hrefs remapped to new_file_name
        """
        # Handle tuple format: (Section, [children])
        if isinstance(toc_entry, tuple):
            first_elem = toc_entry[0]
            if isinstance(first_elem, epub.Section):
                title = getattr(first_elem, 'title', 'Untitled')
                href = getattr(first_elem, 'href', '')
                
                # Remap href to new file, preserve fragment
                if '#' in href:
                    _, fragment = href.split('#', 1)
                    new_href = f"{new_file_name}#{fragment}"
                else:
                    new_href = new_file_name
                
                # Process children if present
                if len(toc_entry) > 1 and isinstance(toc_entry[1], list):
                    child_links = []
                    for idx, child in enumerate(toc_entry[1]):
                        # Recursively process children (they should be Links)
                        if isinstance(child, epub.Link):
                            child_title = getattr(child, 'title', 'Untitled')
                            child_href = getattr(child, 'href', '')
                            
                            # Remap child href
                            if '#' in child_href:
                                _, fragment = child_href.split('#', 1)
                                child_new_href = f"{new_file_name}#{fragment}"
                            else:
                                child_new_href = new_file_name
                            
                            child_links.append(epub.Link(child_new_href, child_title, f"navpoint_{idx}"))
                        elif isinstance(child, tuple):
                            # Recursively handle nested tuples
                            child_links.append(self._build_toc_from_original(child, new_file_name))
                    
                    # Create section with children
                    section_obj = epub.Section(title)
                    section_obj.href = new_href
                    return (section_obj, child_links)
                else:
                    # Section without children
                    return epub.Link(new_href, title, 'navpoint_main')
        
        # Handle Link or Section directly
        elif isinstance(toc_entry, (epub.Link, epub.Section)):
            title = getattr(toc_entry, 'title', 'Untitled')
            href = getattr(toc_entry, 'href', '')
            
            # Remap href
            if '#' in href:
                _, fragment = href.split('#', 1)
                new_href = f"{new_file_name}#{fragment}"
            else:
                new_href = new_file_name
            
            return epub.Link(new_href, title, 'navpoint_main')
        
        # Fallback
        return epub.Link(new_file_name, 'Untitled', 'navpoint_main')

    def _fix_relative_paths_in_content(self, item: epub.EpubHtml, new_file_name: str) -> None:
        """
        Update relative paths in HTML content when moving to a new location.
        """
        import posixpath
        from lxml import html as lxml_html

        if not item.content:
            return

        try:
            # Parse the HTML content
            tree = lxml_html.fromstring(item.content)

            # Get directory of old and new locations
            old_dir = posixpath.dirname(item.file_name) or '.'
            new_dir = posixpath.dirname(new_file_name) or '.'

            # Fix stylesheet links
            for link in tree.xpath('.//link[@rel="stylesheet"]'):
                href = link.get('href', '')
                if href and not href.startswith(('http://', 'https://', 'data:', '/')):
                    # Resolve old relative path to absolute (within EPUB)
                    absolute_path = posixpath.normpath(posixpath.join(old_dir, href))
                    # Calculate new relative path from new location
                    new_href = posixpath.relpath(absolute_path, new_dir)
                    link.set('href', new_href)

            # Fix image sources
            for img in tree.xpath('.//img'):
                src = img.get('src', '')
                if src and not src.startswith(('http://', 'https://', 'data:', '/')):
                    absolute_path = posixpath.normpath(posixpath.join(old_dir, src))
                    new_src = posixpath.relpath(absolute_path, new_dir)
                    img.set('src', new_src)

            # Fix anchor hrefs (for internal links like endnotes.xhtml)
            for anchor in tree.xpath('.//a[@href]'):
                href = anchor.get('href', '')
                if href and not href.startswith(('http://', 'https://', 'mailto:', '#', 'data:')):
                    # Handle fragment separately
                    if '#' in href:
                        path, fragment = href.split('#', 1)
                        fragment = '#' + fragment
                    else:
                        path, fragment = href, ''

                    if path:  # Only fix if there's a path component
                        absolute_path = posixpath.normpath(posixpath.join(old_dir, path))
                        new_path = posixpath.relpath(absolute_path, new_dir)
                        anchor.set('href', new_path + fragment)

            # Update the content
            item.content = lxml_html.tostring(tree, encoding='utf-8')

        except Exception as e:
            print(f"Warning: Error fixing relative paths: {e}")


    def create_epub_from_section(self, section: Dict[str, any], new_title: Optional[str] = None) -> bytes:
        """
        Extract a section (possibly with subsections) and create a new EPUB with proper TOC.
        Builds TOC from the original book's TOC structure, not from the section dict.
        
        Args:
            section: Section dict from analyze() - only used to get href and default title
            new_title: Optional new title for the book (defaults to section title)
            
        Returns:
            New EPUB file as bytes
        """
        if section is None:
            raise ValueError("Section cannot be None")
        
        # Get the main href (strip fragment if present)
        href = section.get('href', '')
        original_href = href  # Keep for TOC lookup
        if '#' in href:
            href = href.split('#')[0]
        
        # Find the main item in the original book
        item = self.find_item_by_href(href)
        if not item:
            raise ValueError(f"No item found for href '{href}'")
        
        # Find the TOC entry in the original book's TOC
        toc_entry = None
        if hasattr(self.book, 'toc') and self.book.toc:
            toc_entry = self._find_toc_entry_by_href(self.book.toc, href)
        
        if not toc_entry:
            # Fallback: create simple TOC from section title
            default_title = section.get('title', 'Untitled Section')
            if not new_title:
                new_title = default_title
        else:
            # Extract title from TOC entry if new_title not provided
            if not new_title:
                if isinstance(toc_entry, tuple) and isinstance(toc_entry[0], epub.Section):
                    new_title = getattr(toc_entry[0], 'title', section.get('title', 'Untitled Section'))
                elif isinstance(toc_entry, (epub.Link, epub.Section)):
                    new_title = getattr(toc_entry, 'title', section.get('title', 'Untitled Section'))
                else:
                    new_title = section.get('title', 'Untitled Section')
        
        # Get metadata
        metadata = self._extracted_metadata or self._extract_metadata()
        
        # Collect dependencies
        images, styles = self._collect_dependencies(item)
        
        # Create new EPUB book
        new_book = epub.EpubBook()
        
        # Set EPUB version
        new_book.EPUB_VERSION = "3.0"
        
        # Copy prefixes from original book
        copy_prefixes(self.book, new_book)
        
        # Set identifier (required)
        identifier = metadata.get('identifier')
        if identifier:
            new_book.set_identifier(identifier)
        else:
            new_book.set_identifier(f"extracted-{new_title}")
        
        # Set title
        new_book.set_title(new_title)
        
        # Set language
        language = metadata.get('language', 'en')
        new_book.set_language(language)
        
        # Add authors
        for author in metadata.get('authors', []):
            new_book.add_author(author)
        
        # Add optional metadata
        if metadata.get('description'):
            new_book.add_metadata('DC', 'description', metadata['description'])
        if metadata.get('rights'):
            new_book.add_metadata('DC', 'rights', metadata['rights'])
        if metadata.get('publisher'):
            new_book.add_metadata('DC', 'publisher', metadata['publisher'])
        if metadata.get('date'):
            new_book.add_metadata('DC', 'date', metadata['date'])
        
        # Reuse the original item but update it for the new book
        # This preserves epub:prefix and all other attributes from original content
        new_file_name = 'section.xhtml'

        self._fix_relative_paths_in_content(item, new_file_name)
        # Update the original item's properties for the new book
        item.file_name = new_file_name
        item.book = new_book  # Point to new book so get_content() uses correct context
        item.title = new_title
        
        new_book.add_item(item)

        # Add cover image if available
        cover_data = self._cover_image or self._extract_cover()
        if cover_data:
            try:
                # Determine cover file extension from magic bytes
                cover_ext = 'jpg'  # Default
                if cover_data.startswith(b'\x89PNG'):
                    cover_ext = 'png'
                elif cover_data.startswith(b'GIF'):
                    cover_ext = 'gif'
                elif cover_data.startswith(b'\xff\xd8'):
                    cover_ext = 'jpg'
                elif cover_data.startswith(b'RIFF') and b'WEBP' in cover_data[:12]:
                    cover_ext = 'webp'
                
                new_book.set_cover(f'cover.{cover_ext}', cover_data)
            except Exception as e:
                print(f"Warning: Could not set cover image: {e}")
        
        # Add styles
        for style in styles:
            new_book.add_item(style)
        
        # Add images
        for img in images:
            new_book.add_item(img)
        
        # Build TOC from original book's TOC entry (not from section dict)
        if toc_entry:
            # Use the TOC entry from the original book
            new_toc_entry = self._build_toc_from_original(toc_entry, new_file_name)
        else:
            # Fallback: create simple TOC link
            new_toc_entry = epub.Link(new_file_name, new_title, 'navpoint_main')
        
        new_book.toc = (new_toc_entry,)
        
        # Add NCX for navigation (ebooklib will generate it from toc)
        new_book.add_item(epub.EpubNcx())
        # Add Nav document (EPUB 3.0 requirement)
        new_book.add_item(epub.EpubNav())

        # Define spine (reading order) - just the content item
        new_book.spine = [item]

        # Debug: Check items before writing
        print("=== Items before write ===")
        for item in new_book.items:  # Access .items directly, not get_items()
            content_len = len(item.content) if item.content else 0
            print(
                f"  type={type(item).__name__}, id={item.id}, file_name={item.file_name}, manifest={item.manifest}, content_bytes={content_len}")

        # Write EPUB to bytes
        output_buffer = io.BytesIO()
        epub.write_epub(output_buffer, new_book)

        # Debug: Check what's actually in the EPUB
        output_buffer.seek(0)
        with zipfile.ZipFile(output_buffer, 'r') as zf:
            print("\n=== Files in generated EPUB ===")
            for name in zf.namelist():
                info = zf.getinfo(name)
                print(f"  {name} ({info.file_size} bytes)")

        output_buffer.seek(0)  # Reset for return


        output_buffer.seek(0)
        epub_bytes = output_buffer.getvalue()
        
        # Validate the generated EPUB (write to temp file for validation)
        try:
            with tempfile.NamedTemporaryFile(suffix='.epub', delete=False) as tmp:
                tmp.write(epub_bytes)
                tmp_path = tmp.name
            self._validate_epub(tmp_path, f"extract: {new_title}")
            os.unlink(tmp_path)  # Clean up temp file
        except Exception as e:
            print(f"[EPUB-VALIDATION] Warning: Could not validate extracted EPUB: {e}")
        return epub_bytes
    
    def create_epub_with_new_cover(self, cover_image_data: bytes) -> bytes:
        """
        Create a copy of the EPUB with a different cover image.
        
        This method copies the entire EPUB at the zip level, only replacing
        the cover image file. This preserves all content, metadata, and 
        structure exactly as in the original.
        
        Args:
            cover_image_data: New cover image as bytes (any format - PNG, JPEG, WEBP, GIF)
            
        Returns:
            New EPUB file as bytes with the cover replaced
        """
        # Convert cover to JPEG for maximum EPUB reader compatibility
        if cover_image_data.startswith(b'\xff\xd8'):
            final_cover_data = cover_image_data
        else:
            # Convert to JPEG
            img = Image.open(io.BytesIO(cover_image_data))
            
            # Convert to RGB if needed (RGBA, P mode need conversion)
            if img.mode in ('RGBA', 'LA', 'P'):
                background = Image.new('RGB', img.size, (255, 255, 255))
                if img.mode == 'P':
                    img = img.convert('RGBA')
                if img.mode in ('RGBA', 'LA'):
                    background.paste(img, mask=img.split()[-1])
                    img = background
                else:
                    img = img.convert('RGB')
            elif img.mode != 'RGB':
                img = img.convert('RGB')
            
            # Save as JPEG
            jpg_buffer = io.BytesIO()
            img.save(jpg_buffer, format='JPEG', quality=95)
            final_cover_data = jpg_buffer.getvalue()
        
        # Get cover image path from ebooklib (already loaded in self.book)
        cover_item = next(self.book.get_items_of_type(ebooklib.ITEM_COVER), None)
        if not cover_item:
            raise ValueError("Could not find cover image in the original EPUB")
        
        # Cover path in the EPUB is FOLDER_NAME/file_name (e.g., "EPUB/cover.jpg")
        cover_path = f"{self.book.FOLDER_NAME}/{cover_item.file_name}"
        
        # Open original EPUB
        with zipfile.ZipFile(str(self.epub_path), 'r') as src_zip:
            
            # Create new EPUB in memory
            output_buffer = io.BytesIO()
            
            with zipfile.ZipFile(output_buffer, 'w', zipfile.ZIP_DEFLATED) as dst_zip:
                for item in src_zip.infolist():
                    if item.filename == cover_path:
                        # Replace cover image with new data
                        # Preserve the original compression type for mimetype
                        dst_zip.writestr(item, final_cover_data)
                    elif item.filename == 'mimetype':
                        # mimetype must be stored uncompressed and first
                        dst_zip.writestr(item, src_zip.read(item.filename), compress_type=zipfile.ZIP_STORED)
                    else:
                        # Copy file as-is
                        dst_zip.writestr(item, src_zip.read(item.filename))
        
        output_buffer.seek(0)
        return output_buffer.getvalue()
    
    @staticmethod
    def replace_cover_image_in_file(epub_path: str, cover_image_data: bytes) -> bool:
        """Replace the cover image in an existing EPUB file (modifies file in place).
        
        Reads the EPUB, sets the new cover, and writes it back.
        Converts non-JPEG images to JPEG for maximum compatibility.
        
        Args:
            epub_path: Path to the EPUB file
            cover_image_data: Cover image as bytes (any format - PNG, JPEG, WEBP, GIF)
            
        Returns:
            bool: True if cover was updated successfully, False otherwise
        """
        try:
            epub_path = Path(epub_path)

            # Convert cover to JPEG for maximum EPUB reader compatibility
            # Check if already JPEG
            if cover_image_data.startswith(b'\xff\xd8'):
                jpeg_cover_data = cover_image_data
            else:
                # Convert to JPEG
                img = Image.open(io.BytesIO(cover_image_data))
                
                # Convert to RGB if needed (RGBA, P mode need conversion)
                if img.mode in ('RGBA', 'LA', 'P'):
                    background = Image.new('RGB', img.size, (255, 255, 255))
                    if img.mode == 'P':
                        img = img.convert('RGBA')
                    if img.mode in ('RGBA', 'LA'):
                        background.paste(img, mask=img.split()[-1])
                        img = background
                    else:
                        img = img.convert('RGB')
                elif img.mode != 'RGB':
                    img = img.convert('RGB')
                
                # Save as JPEG
                jpg_buffer = io.BytesIO()
                img.save(jpg_buffer, format='JPEG', quality=95)
                jpeg_cover_data = jpg_buffer.getvalue()
            
            # Read the existing EPUB (ignore_ncx for EPUB 3 compatibility - NCX is optional)
            book = epub.read_epub(epub_path)
            
            # Set the new cover using ebooklib's set_cover method
            # This handles all the EPUB metadata (manifest, guide, metadata) properly
            book.set_cover('cover.jpg', jpeg_cover_data)
            
            # Write the updated EPUB back to a temporary file first
            temp_fd, temp_path = tempfile.mkstemp(suffix='.epub')
            try:
                os.close(temp_fd)
                epub.write_epub(temp_path, book)
                
                # Replace original with new file
                shutil.move(temp_path, epub_path)
                return True
            except Exception as e:
                # Clean up temp file on error
                if os.path.exists(temp_path):
                    os.unlink(temp_path)
                raise e
            
        except Exception as e:
            print(f"Error replacing EPUB cover: {e}")
            traceback.print_exc()
            return False

