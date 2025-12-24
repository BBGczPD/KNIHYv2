import os
import sys
import re
import shutil
import zipfile
import tempfile
import xml.etree.ElementTree as ET
import subprocess
import threading
import webbrowser
import urllib.parse
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Iterator, Optional, Tuple, List, Dict, Set

from PySide6 import QtCore, QtGui, QtWidgets

try:
    from send2trash import send2trash
    SEND2TRASH_AVAILABLE = True
except ImportError:
    send2trash = None
    SEND2TRASH_AVAILABLE = False

try:
    import requests
    from bs4 import BeautifulSoup
    WEBLIBS_AVAILABLE = True
except ImportError:
    requests = None
    BeautifulSoup = None
    WEBLIBS_AVAILABLE = False

APP_TITLE = "EPUB Studio – clean build (v3)"
APP_VERSION = "3.0"

SUPPORTED_IN: Set[str] = {".epub", ".mobi", ".azw3", ".pdf", ".doc", ".docx"}
LIGHT_EXT: Set[str] = {".epub", ".mobi", ".azw3"}
HEAVY_EXT: Set[str] = {".pdf", ".doc", ".docx"}

CLEAN_PROFILE = "Standardní"

DEFAULT_LIGHT = 8
DEFAULT_HEAVY = 3
THREAD_RESERVE = 2

COLOR_BG = "#0b0d12"
COLOR_PANEL = "#12141b"
COLOR_BLOCK = "#141720"
COLOR_INPUT = "#0d0f14"
COLOR_ACCENT = "#8b1d2c"
COLOR_TEXT = "#e6e6e6"

CSS_BASE = """
@namespace epub "http://www.idpf.org/2007/ops";
html,body{font-family:Roboto, Arial, Helvetica, sans-serif; font-size:12pt;}
body{line-height:1.35;}
p{margin:0 0 0.85em 0;}
img{max-width:100%; height:auto;}
h1,h2,h3{margin:1.2em 0 0.6em 0;}
"""

WIN_BAD_CHARS = r'<>:"/\\|?*'
WEB_TIMEOUT = 10

def which(cmd: str) -> bool:
    return shutil.which(cmd) is not None

def run(cmd: List[str], cwd: Optional[str] = None) -> Tuple[bool, str]:
    try:
        startupinfo = None
        creationflags = 0
        if sys.platform.startswith("win"):
            startupinfo = subprocess.STARTUPINFO()
            startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
            creationflags = subprocess.CREATE_NO_WINDOW
        process = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            cwd=cwd,
            text=True,
            encoding="utf-8",
            errors="replace",
            startupinfo=startupinfo,
            creationflags=creationflags,
        )
        return (process.returncode == 0, process.stdout)
    except FileNotFoundError:
        return (False, f"[ERROR] Command not found: {cmd[0]}")
    except Exception as e:
        return (False, f"[EXEC ERROR] {e}")

def is_supported(p: Path) -> bool:
    return p.is_file() and p.suffix.lower() in SUPPORTED_IN

def find_books(folder: Path) -> Iterator[Path]:
    for root, _, files in os.walk(folder):
        for f in files:
            p = Path(root) / f
            if is_supported(p):
                yield p

def simple_validity_check(p: Path) -> bool:
    ext = p.suffix.lower()
    try:
        if ext == ".epub":
            with zipfile.ZipFile(p, 'r') as z:
                return "META-INF/container.xml" in z.namelist()
        if ext == ".pdf":
            with open(p, 'rb') as f:
                return f.read(5) == b"%PDF-"
        if ext == ".docx":
            with zipfile.ZipFile(p, 'r') as z:
                return "[Content_Types].xml" in z.namelist()
        if ext == ".mobi":
            with open(p, 'rb') as f:
                return b"BOOKMOBI" in f.read(4096)
        if ext == ".azw3":
            with open(p, 'rb') as f:
                blob = f.read(8192)
                return (b"BKEX" in blob) or (b"EXTH" in blob)
        if ext == ".doc":
            return True
    except (OSError, zipfile.BadZipFile):
        return False
    return False

def _profile_args() -> List[str]:
    return [
        "--epub-version",
        "3",
        "--output-profile",
        "tablet",
        "--language",
        "cs",
        "--dont-split-on-page-breaks",
        "--line-height",
        "130",
        "--base-font-size",
        "12",
        "--margin-left",
        "18",
        "--margin-right",
        "18",
        "--filter-css",
        "font-family,font-size",
    ]

def _pdf_extra_args() -> List[str]:
    return ["--enable-heuristics", "--pdf-default-font-size", "12"]

def _extra_css_args() -> List[str]:
    return ["--extra-css", CSS_BASE.strip()]

def build_calibre_args() -> List[str]:
    args = _profile_args()
    args += _extra_css_args()
    return args

def _write_error_file(input_path: Path, text: str) -> None:
    try:
        error_file = input_path.parent / f"{input_path.stem}_error.txt"
        error_file.write_text(text, encoding="utf-8", errors="replace")
    except OSError:
        pass

def _clean_paragraph_inner(html: str) -> Tuple[str, int, int]:
    br_hits = len(re.findall(r"(<br\s*/?>\s*){2,}", html, flags=re.IGNORECASE))
    space_hits = len(re.findall(r"(?:&nbsp;|\u00a0|\s){2,}", html))
    cleaned = re.sub(r"(<br\s*/?>\s*){2,}", "<br/>", html, flags=re.IGNORECASE)
    cleaned = re.sub(r"\s*(<br\s*/?>)\s*", r"\1", cleaned, flags=re.IGNORECASE)
    cleaned = re.sub(r"(?:&nbsp;|\u00a0)+", " ", cleaned)
    cleaned = re.sub(r"\s{2,}", " ", cleaned)
    return cleaned, space_hits, br_hits


def _merge_soft_wrapped_paragraphs(html_text: str) -> str:
    para_re = re.compile(r"(<p[^>]*>)(.*?)(</p>)", flags=re.IGNORECASE | re.DOTALL)
    matches = list(para_re.finditer(html_text))
    if len(matches) < 2:
        return html_text

    def _plain(text: str) -> str:
        return re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", text)).strip()

    def _first_letter(text: str) -> Optional[str]:
        match = re.search(r"[\"'„“«»([{]*\s*([A-Za-zÀ-ž])", text)
        return match.group(1) if match else None

    def _is_heading_like(text: str, open_tag: str) -> bool:
        if re.search(r'class="[^"]*(title|chapter|heading)[^"]*"', open_tag, flags=re.IGNORECASE):
            return True
        if not text:
            return False
        if len(text) <= 60 and text.upper() == text:
            return True
        return False

    pieces: List[str] = []
    cursor = 0
    i = 0
    while i < len(matches):
        current = matches[i]
        if i < len(matches) - 1:
            nxt = matches[i + 1]
            prev_text = _plain(current.group(2))
            next_text = _plain(nxt.group(2))
            if prev_text and next_text:
                if re.search(r"[.?!:]\s*$", prev_text):
                    pass
                elif _is_heading_like(prev_text, current.group(1)) or _is_heading_like(next_text, nxt.group(1)):
                    pass
                elif "<img" in current.group(2).lower() or "<img" in nxt.group(2).lower():
                    pass
                else:
                    first_letter = _first_letter(next_text)
                    if first_letter and first_letter.islower():
                        merged_inner = current.group(2).rstrip() + " " + nxt.group(2).lstrip()
                        merged_inner = re.sub(r"\s{2,}", " ", merged_inner)
                        merged_html = f"{current.group(1)}{merged_inner}{current.group(3)}"
                        pieces.append(html_text[cursor:current.start()])
                        pieces.append(merged_html)
                        cursor = nxt.end()
                        i += 2
                        continue
        pieces.append(html_text[cursor:current.end()])
        cursor = current.end()
        i += 1
    pieces.append(html_text[cursor:])
    return "".join(pieces)


def _process_html_content(text: str, stats: Dict[str, int], asset_root: Optional[Path] = None) -> Tuple[str, List[str]]:
    last_empty = False
    missing_images: List[str] = []
    para_re = re.compile(r"(<p[^>]*>)(.*?)(</p>)", flags=re.IGNORECASE | re.DOTALL)

    def repl(match: re.Match) -> str:
        nonlocal last_empty
        open_tag, inner, close_tag = match.groups()
        inner_text = re.sub(r"<[^>]+>", " ", inner)
        normalized = re.sub(r"[\s\u00a0]+", "", inner_text)
        if normalized.isdigit() and normalized:
            stats["removed_markers"] = stats.get("removed_markers", 0) + 1
            last_empty = False
            return ""
        if not normalized:
            stats["removed_markers"] = stats.get("removed_markers", 0) + 1
            last_empty = False
            return ""

        cleaned_inner, space_hits, br_hits = _clean_paragraph_inner(inner)
        if space_hits or br_hits or cleaned_inner != inner:
            stats["cleaned_paragraphs"] = stats.get("cleaned_paragraphs", 0) + 1
        inner_after = re.sub(r"<[^>]+>", " ", cleaned_inner)
        normalized_after = re.sub(r"[\s\u00a0]+", "", inner_after)
        if not normalized_after:
            if last_empty:
                stats["collapsed_empty_paragraphs"] = stats.get("collapsed_empty_paragraphs", 0) + 1
                return ""
            last_empty = True
        else:
            last_empty = False
        return f"{open_tag}{cleaned_inner}{close_tag}"

    cleaned_text = para_re.sub(repl, text)
    cleaned_text = _merge_soft_wrapped_paragraphs(cleaned_text)

    if asset_root and WEBLIBS_AVAILABLE and BeautifulSoup:
        try:
            soup = BeautifulSoup(cleaned_text, "html.parser")
            for img in soup.find_all("img"):
                src = (img.get("src") or "").strip()
                if not src:
                    continue
                img_path = (asset_root / src).resolve()
                if not img_path.exists():
                    missing_images.append(src)
                    img.replace_with(BeautifulSoup("<!--img-removed-->", "html.parser"))
            cleaned_text = soup.decode()
        except Exception:
            pass

    return cleaned_text, missing_images


def _cleanup_page_markers_in_epub(epub_path: Path) -> Dict[str, int]:
    stats: Dict[str, int] = {"touched_files": 0, "removed_markers": 0, "cleaned_paragraphs": 0, "collapsed_empty_paragraphs": 0}
    try:
        tmpfd, tmpzip = tempfile.mkstemp(suffix=".epub")
        os.close(tmpfd)
        with zipfile.ZipFile(epub_path, "r") as zin, zipfile.ZipFile(tmpzip, "w", compression=zipfile.ZIP_DEFLATED) as zout:
            for item in zin.infolist():
                data = zin.read(item.filename)
                lower = item.filename.lower()
                changed = False
                if lower.endswith((".xhtml", ".html", ".htm")):
                    try:
                        text = data.decode("utf-8", errors="replace")
                        new_text, _ = _process_html_content(text, stats)
                        if new_text != text:
                            changed = True
                            data = new_text.encode("utf-8")
                    except (UnicodeDecodeError, UnicodeEncodeError):
                        pass
                if changed:
                    stats["touched_files"] += 1
                zout.writestr(item, data)
        shutil.move(tmpzip, epub_path)
    except (OSError, zipfile.BadZipFile):
        pass
    return stats


def analyze_epub_structure(epub_path: Path) -> Dict[str, object]:
    report: Dict[str, object] = {"files": [], "errors": []}
    try:
        with zipfile.ZipFile(epub_path, "r") as zf:
            for item in zf.infolist():
                lower = item.filename.lower()
                if not lower.endswith((".xhtml", ".html", ".htm")):
                    continue
                try:
                    raw = zf.read(item.filename).decode("utf-8", errors="replace")
                except UnicodeDecodeError:
                    report["errors"].append(f"Problém s kódováním: {item.filename}")
                    continue
                text_plain = re.sub(r"<[^>]+>", " ", raw)
                alnum_chars = sum(1 for ch in text_plain if ch.isalnum())
                img_count = len(re.findall(r"<img\b", raw, flags=re.IGNORECASE))
                paragraphs = re.findall(r"<p[^>]*>.*?</p>", raw, flags=re.IGNORECASE | re.DOTALL)
                nbsp_only_p = 0
                max_consec_empty_p = 0
                current_run = 0
                for p in paragraphs:
                    inner = re.sub(r"<[^>]+>", " ", p)
                    normalized = re.sub(r"[\s\u00a0]+", "", inner)
                    if not normalized:
                        nbsp_only_p += 1
                        current_run += 1
                        max_consec_empty_p = max(max_consec_empty_p, current_run)
                    else:
                        current_run = 0
                sample_text = re.sub(r"\s+", " ", text_plain).strip()[:200]
                page_type = "keep"
                if alnum_chars == 0 and img_count:
                    page_type = "image_page"
                elif alnum_chars == 0:
                    page_type = "empty"
                elif alnum_chars < 40 and img_count == 0:
                    page_type = "heading"
                elif nbsp_only_p > 0 or max_consec_empty_p > 1:
                    page_type = "needs_cleaning"
                report["files"].append(
                    {
                        "name": item.filename,
                        "alnum_chars": alnum_chars,
                        "img_count": img_count,
                        "nbsp_only_p": nbsp_only_p,
                        "max_consec_empty_p": max_consec_empty_p,
                        "sample_text": sample_text,
                        "type": page_type,
                    }
                )
    except (OSError, zipfile.BadZipFile) as exc:
        report["errors"].append(str(exc))
    return report


def generate_change_summary(changes: Dict[str, object]) -> str:
    files: List[Dict[str, object]] = changes.get("files", []) if isinstance(changes, dict) else []
    totals = {"empty": 0, "needs_cleaning": 0, "image_page": 0, "heading": 0, "keep": 0}
    for item in files:
        typ = item.get("type", "keep")
        if typ in totals:
            totals[typ] += 1
    lines = [
        f"Stránky: {len(files)}",
        f"Prázdné k odstranění: {totals['empty']}",
        f"K očištění: {totals['needs_cleaning']}",
        f"Obrazové: {totals['image_page']}",
        f"Nadpisy/ostatní: {totals['heading'] + totals['keep']}",
    ]
    errors = changes.get("errors")
    if errors:
        lines.append("Chyby: " + "; ".join(str(e) for e in errors))
    sample_dirty = [f["name"] for f in files if f.get("type") == "needs_cleaning"][:3]
    if sample_dirty:
        lines.append("K očištění: " + ", ".join(sample_dirty))
    sample_empty = [f["name"] for f in files if f.get("type") == "empty"][:3]
    if sample_empty:
        lines.append("K odebrání: " + ", ".join(sample_empty))
    return "\n".join(lines)


def _update_content_opf(opf_path: Path, removed_files: Set[str]) -> None:
    if not opf_path.exists() or not removed_files:
        return
    try:
        tree = ET.parse(opf_path)
        root = tree.getroot()
        ns = {"opf": root.tag.split('}')[0].strip('{') if '}' in root.tag else ''}
        manifest = root.find(".//opf:manifest", ns)
        spine = root.find(".//opf:spine", ns)
        removed_ids: Set[str] = set()
        if manifest is not None:
            for item in list(manifest):
                href = item.get("href", "")
                if href in removed_files:
                    removed_ids.add(item.get("id", ""))
                    manifest.remove(item)
        if spine is not None and removed_ids:
            for itemref in list(spine):
                if itemref.get("idref", "") in removed_ids:
                    spine.remove(itemref)
        tree.write(opf_path, encoding="utf-8", xml_declaration=True)
    except Exception:
        pass


def apply_epub_fixes(epub_path: Path, changes: Dict[str, object], dry_run: bool = False) -> Dict[str, object]:
    files: List[Dict[str, object]] = changes.get("files", []) if isinstance(changes, dict) else []
    to_delete = [f["name"] for f in files if f.get("type") == "empty"]
    to_clean = [f["name"] for f in files if f.get("type") == "needs_cleaning"]
    kept = [f["name"] for f in files if f.get("type") not in {"empty", "needs_cleaning"}]
    result: Dict[str, object] = {
        "deleted": to_delete,
        "cleaned": to_clean,
        "kept": kept,
        "backup": None,
        "report": [],
    }
    if dry_run:
        return result

    backup = epub_path.with_name(epub_path.stem + "_old.epub")
    try:
        shutil.copy2(epub_path, backup)
        result["backup"] = str(backup)
    except OSError:
        result.setdefault("errors", []).append("Backup selhal, pokračuji bez něj.")

    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = Path(tmpdir)
        try:
            with zipfile.ZipFile(epub_path, "r") as zin:
                zin.extractall(tmpdir_path)
        except (OSError, zipfile.BadZipFile) as exc:
            result.setdefault("errors", []).append(str(exc))
            return result

        removed_set: Set[str] = set()
        for rel_path in to_delete:
            target = tmpdir_path / rel_path
            if target.exists():
                try:
                    target.unlink()
                    removed_set.add(rel_path)
                except OSError:
                    result.setdefault("errors", []).append(f"Nelze odstranit {rel_path}")

        cleaning_stats: Dict[str, int] = {}
        missing_assets: List[str] = []
        for rel_path in to_clean:
            file_path = tmpdir_path / rel_path
            if not file_path.exists():
                continue
            try:
                text = file_path.read_text(encoding="utf-8", errors="replace")
                cleaned, missing = _process_html_content(text, cleaning_stats, asset_root=tmpdir_path)
                if cleaned != text:
                    file_path.write_text(cleaned, encoding="utf-8")
                missing_assets.extend(missing)
            except OSError:
                result.setdefault("errors", []).append(f"Nelze čistit {rel_path}")

        opf_files = list(tmpdir_path.glob("**/*.opf"))
        if opf_files and removed_set:
            _update_content_opf(opf_files[0], removed_set)

        new_epub = tmpdir_path / "rebuilt.epub"
        with zipfile.ZipFile(new_epub, "w") as zout:
            mime = tmpdir_path / "mimetype"
            if mime.exists():
                zout.write(mime, arcname="mimetype", compress_type=zipfile.ZIP_STORED)
            for root_dir, _, filenames in os.walk(tmpdir_path):
                for filename in filenames:
                    full_path = Path(root_dir) / filename
                    if full_path == new_epub or full_path.name == "mimetype":
                        continue
                    arcname = full_path.relative_to(tmpdir_path)
                    zout.write(full_path, arcname=arcname, compress_type=zipfile.ZIP_DEFLATED)

        try:
            shutil.move(str(new_epub), str(epub_path))
        except OSError as exc:
            result.setdefault("errors", []).append(f"Nelze přepsat EPUB: {exc}")

        if cleaning_stats:
            result["cleaning_stats"] = cleaning_stats
        if missing_assets:
            result["report"].append(f"Chybějící obrázky nahrazeny: {', '.join(sorted(set(missing_assets)))}")

    return result

def _safe_replace(orig: Path, new_file: Path) -> bool:
    try:
        if orig.exists():
            orig.unlink()
        shutil.move(str(new_file), str(orig))
        return True
    except OSError:
        return False

def _trash(path: Path) -> None:
    if SEND2TRASH_AVAILABLE:
        try:
            send2trash(str(path))
            return
        except Exception:
            pass
    try:
        if path.is_file():
            path.unlink(missing_ok=True)
    except OSError:
        pass

def _finalize_files(input_path: Path, produced_epub: Path, was_epub_input: bool) -> Tuple[bool, str]:
    try:
        target = input_path.with_suffix(".epub")
        if was_epub_input:
            temp_out = input_path.with_name(input_path.stem + "_temp.epub")
            if produced_epub != temp_out and produced_epub.exists():
                if temp_out.exists():
                    temp_out.unlink()
                shutil.move(str(produced_epub), str(temp_out))
            old = input_path.with_name(input_path.stem + "_old" + input_path.suffix)
            if old.exists():
                old.unlink()
            shutil.move(str(input_path), str(old))
            if not _safe_replace(input_path.with_suffix(".epub"), temp_out):
                shutil.move(str(old), str(input_path))
                return (False, "Chyba přepisu výstupu")
            _trash(old)
            return (True, str(target))
        else:
            old = input_path.with_name(input_path.stem + "_old" + input_path.suffix)
            if old.exists():
                old.unlink()
            shutil.move(str(input_path), str(old))

            # Pokud Calibre vytvořilo výstup se stejným názvem jako cílový soubor,
            # nesmíme jej smazat před přesunem (typicky .mobi -> .epub).
            if produced_epub != target and target.exists():
                target.unlink()

            if produced_epub == target:
                # Výstup už je na správném místě; jen ověříme, že existuje.
                if not target.exists():
                    return (False, "Chyba finalizace: výstupní soubor nebyl nalezen")
            else:
                shutil.move(str(produced_epub), str(target))

            _trash(old)
            return (True, str(target))
    except OSError as e:
        return (False, f"Chyba finalizace: {e}")

def convert_one(input_path: Path) -> Tuple[bool, Optional[Path], str]:
    input_path = input_path.resolve()
    was_epub_input = (input_path.suffix.lower() == ".epub")
    try:
        if not simple_validity_check(input_path):
            msg = "Neprošla rychlá validace."
            _write_error_file(input_path, msg)
            return (False, None, msg)
        if not was_epub_input:
            raw_out = input_path.with_suffix(".epub")
        else:
            raw_out = input_path.with_name(input_path.stem + "_temp.epub")
        if raw_out.exists():
            raw_out.unlink()
        args = ["ebook-convert", str(input_path), str(raw_out)]
        args += build_calibre_args()
        if input_path.suffix.lower() == ".pdf":
            args += _pdf_extra_args()
        ok, output = run(args)
        if not ok:
            _write_error_file(input_path, output)
            if raw_out.exists():
                raw_out.unlink(missing_ok=True)
            return (False, None, "Chyba převodu (viz _error.txt)")
        _cleanup_page_markers_in_epub(raw_out)
        fin_ok, fin_msg = _finalize_files(input_path, raw_out, was_epub_input)
        if not fin_ok:
            _write_error_file(input_path, fin_msg)
            if raw_out.exists():
                raw_out.unlink(missing_ok=True)
            return (False, None, fin_msg)
        return (True, Path(fin_msg), "OK")
    except Exception as e:
        msg = f"Výjimka: {e}"
        _write_error_file(input_path, msg)
        return (False, None, msg)

def _parse_ebook_meta_output(text: str) -> Dict[str, str]:
    md = {}
    for line in text.splitlines():
        line = line.strip()
        if not line or ":" not in line:
            continue
        parts = line.split(":", 1)
        if len(parts) != 2:
            continue
        key, val = parts
        key = key.strip().lower()
        val = val.strip()
        if key in ("title", "název", "nazev"):
            md["title"] = val
        elif key in ("author(s)", "authors", "autor", "autoři", "autori"):
            md["authors"] = val
        elif key in ("series", "série", "serie"):
            md["series"] = val
        elif key in ("series index", "series_index", "pořadí v sérii", "poради v serii", "index"):
            md["series index"] = val
        elif key in ("language", "jazyk"):
            md["language"] = val
        elif key in ("tags", "štítky", "stitky"):
            md["tags"] = val
        elif key in ("isbn"):
            md["isbn"] = val
        elif key in ("identifiers"):
            if "isbn:" in val.lower():
                for part in val.split(","):
                    if "isbn:" in part.lower():
                        isbn_val = part.split(":", 1)[1].strip()
                        md["isbn"] = isbn_val
    return md

def _parse_opf_metadata(opf_path: Path) -> Dict[str, str]:
    md: Dict[str, str] = {}
    try:
        tree = ET.parse(opf_path)
        root = tree.getroot()
    except (ET.ParseError, OSError):
        return md
    opf_ns = root.tag.split("}")[0].strip("{") if "}" in root.tag else ""
    dc_ns = "http://purl.org/dc/elements/1.1/"
    ns = {"opf": opf_ns, "dc": dc_ns}
    metadata = root.find(".//opf:metadata", ns) if opf_ns else root.find(".//metadata")
    if metadata is None:
        return md

    title_node = metadata.find("dc:title", ns)
    if title_node is not None and title_node.text:
        md["title"] = title_node.text.strip()

    authors = [node.text.strip() for node in metadata.findall("dc:creator", ns) if node.text and node.text.strip()]
    if authors:
        md["authors"] = "; ".join(authors)

    lang_node = metadata.find("dc:language", ns)
    if lang_node is not None and lang_node.text:
        md["language"] = lang_node.text.strip()

    tags = [node.text.strip() for node in metadata.findall("dc:subject", ns) if node.text and node.text.strip()]
    if tags:
        md["tags"] = ", ".join(tags)

    isbn = ""
    for ident in metadata.findall("dc:identifier", ns):
        scheme = ident.attrib.get(f"{{{opf_ns}}}scheme") if opf_ns else ident.attrib.get("scheme", "")
        ident_text = ident.text or ""
        if (scheme or "").upper() == "ISBN" or "isbn" in ident_text.lower():
            isbn = ident_text
            break
    if isbn:
        md["isbn"] = re.sub(r"[^0-9Xx]", "", isbn).upper()

    series = ""
    series_index = ""
    for meta in metadata.findall("opf:meta", ns) if opf_ns else metadata.findall("meta"):
        name = (meta.attrib.get("name") or meta.attrib.get("property") or "").strip()
        content = (meta.attrib.get("content") or meta.text or "").strip()
        if name == "calibre:series":
            series = content
        elif name == "calibre:series_index":
            series_index = content
    if series:
        md["series"] = series
    if series_index:
        md["series index"] = series_index
    return md


def read_metadata(path: Path) -> Dict[str, str]:
    if not which("ebook-meta"):
        return {}
    fd, tmp_name = tempfile.mkstemp(suffix=".opf")
    os.close(fd)
    tmp = Path(tmp_name)
    try:
        ok, output = run(["ebook-meta", str(path), "--to-opf", str(tmp)])
        if ok and tmp.exists():
            return _parse_opf_metadata(tmp)
        ok, output = run(["ebook-meta", str(path)])
        return _parse_ebook_meta_output(output) if ok else {}
    finally:
        tmp.unlink(missing_ok=True)


def _update_opf_metadata(opf_path: Path, md: Dict[str, str]) -> bool:
    try:
        tree = ET.parse(opf_path)
        root = tree.getroot()
    except (ET.ParseError, OSError):
        return False
    opf_ns = root.tag.split("}")[0].strip("{") if "}" in root.tag else ""
    dc_ns = "http://purl.org/dc/elements/1.1/"
    ns = {"opf": opf_ns, "dc": dc_ns}
    metadata = root.find(".//opf:metadata", ns) if opf_ns else root.find(".//metadata")
    if metadata is None:
        return False

    def _remove_all(tag: str) -> None:
        for node in list(metadata.findall(tag, ns)):
            metadata.remove(node)

    _remove_all("dc:title")
    _remove_all("dc:creator")
    _remove_all("dc:language")
    _remove_all("dc:subject")

    for ident in list(metadata.findall("dc:identifier", ns)):
        scheme = ident.attrib.get(f"{{{opf_ns}}}scheme") if opf_ns else ident.attrib.get("scheme", "")
        ident_text = ident.text or ""
        if (scheme or "").upper() == "ISBN" or "isbn" in ident_text.lower():
            metadata.remove(ident)

    for meta in list(metadata.findall("opf:meta", ns) if opf_ns else metadata.findall("meta")):
        name = (meta.attrib.get("name") or meta.attrib.get("property") or "").strip()
        if name in {"calibre:series", "calibre:series_index"}:
            metadata.remove(meta)

    title = md.get("title")
    if title:
        ET.SubElement(metadata, f"{{{dc_ns}}}title").text = title
    authors = [a.strip() for a in (md.get("authors") or "").split(";") if a.strip()]
    for author in authors:
        ET.SubElement(metadata, f"{{{dc_ns}}}creator").text = author
    language = md.get("language")
    if language:
        ET.SubElement(metadata, f"{{{dc_ns}}}language").text = language
    tags = [t.strip() for t in re.split(r"[;,]", md.get("tags") or "") if t.strip()]
    for tag in tags:
        ET.SubElement(metadata, f"{{{dc_ns}}}subject").text = tag
    isbn = md.get("isbn")
    if isbn:
        ident = ET.SubElement(metadata, f"{{{dc_ns}}}identifier")
        if opf_ns:
            ident.attrib[f"{{{opf_ns}}}scheme"] = "ISBN"
        else:
            ident.attrib["scheme"] = "ISBN"
        ident.text = isbn
    series = md.get("series")
    series_index = md.get("series index")
    if series:
        meta = ET.SubElement(metadata, f"{{{opf_ns}}}meta" if opf_ns else "meta")
        meta.attrib["name"] = "calibre:series"
        meta.attrib["content"] = series
    if series_index:
        meta = ET.SubElement(metadata, f"{{{opf_ns}}}meta" if opf_ns else "meta")
        meta.attrib["name"] = "calibre:series_index"
        meta.attrib["content"] = series_index
    tree.write(opf_path, encoding="utf-8", xml_declaration=True)
    return True


def write_metadata(path: Path, md: Dict[str, str]) -> bool:
    if not path.exists():
        return False
    md = _clean_metadata_fields(md)
    if not md.get("language"):
        md["language"] = "cs"
    if not which("ebook-meta"):
        _write_error_file(path, "ebook-meta není v PATH.")
        return False
    fd, tmp_name = tempfile.mkstemp(suffix=".opf")
    os.close(fd)
    tmp = Path(tmp_name)
    try:
        ok, output = run(["ebook-meta", str(path), "--to-opf", str(tmp)])
        if ok and tmp.exists() and _update_opf_metadata(tmp, md):
            ok, output = run(["ebook-meta", str(path), "--from-opf", str(tmp)])
            if not ok:
                _write_error_file(path, output)
            return ok
        cmd = ["ebook-meta", str(path)]

        def add_arg(arg: str, key: str, allow_empty: bool = True) -> None:
            val = (md.get(key) or "").strip()
            if not val and not allow_empty:
                return
            cmd.extend([arg, val])

        add_arg("--title", "title")
        add_arg("--authors", "authors")
        add_arg("--series", "series")
        add_arg("--index", "series index", allow_empty=False)
        add_arg("--language", "language")
        add_arg("--tags", "tags")
        add_arg("--isbn", "isbn")
        ok, output = run(cmd)
        if not ok:
            _write_error_file(path, output)
        return ok
    finally:
        tmp.unlink(missing_ok=True)

def _sanitize_filename(name: str) -> str:
    name = "".join(ch for ch in name if ch not in WIN_BAD_CHARS)
    name = re.sub(r"\s+", " ", name).strip()
    return name

def build_filename_from_md(md: Dict[str, str]) -> Optional[str]:
    title = md.get("title", "").strip()
    series = md.get("series", "").strip()
    sidx = _normalize_series_index(md.get("series index", ""))
    if not title:
        return None
    parts = []
    if series and sidx:
        idx_fmt = f"{int(float(sidx)):02d}" if sidx.replace(".", "", 1).isdigit() else sidx
        parts.append(f"{idx_fmt} {series}")
    parts.append(title)
    return _sanitize_filename(" ".join(parts))


def guess_metadata_from_filename(path: Path) -> Dict[str, str]:
    name = path.stem
    parts = [p.strip() for p in name.split(" - ") if p.strip()]
    result: Dict[str, str] = {}
    if len(parts) >= 2:
        result["authors"] = parts[-1]
        result["title"] = " - ".join(parts[:-1])
    elif len(parts) == 1:
        result["title"] = parts[0]
    series_match = re.search(r"\((\d+(?:\.\d+)?)\)$", result.get("title", ""))
    if series_match:
        result["series index"] = series_match.group(1)
        cleaned = re.sub(r"\s*\(\d+(?:\.\d+)?\)$", "", result["title"])
        result["title"] = cleaned.strip()
    return result


def _dedup_authors(authors: str) -> str:
    """Odstraní duplicitní autory a šumy typu „a kol."."""
    if not authors:
        return ""

    flattened = re.sub(r"\[([^\]]+)\]", r";\1;", authors)
    flattened = re.sub(r"[|/]+", ";", flattened)
    flattened = re.sub(r"\s+(?:&|and|a)\s+", ";", flattened, flags=re.IGNORECASE)
    flattened = re.sub(r"\s*a\s+kol\.?,?", ";", flattened, flags=re.IGNORECASE)
    flattened = re.sub(r";{2,}", ";", flattened)

    parts = [p.strip(" ,;") for p in flattened.split(";") if p.strip(" ,;")]
    if len(parts) == 1 and parts[0].count(",") >= 2:
        candidate = parts[0]
        split_parts = [p.strip(" ,") for p in re.split(r",\s*(?=[A-ZÁČĎÉĚÍĽĹŇÓÔŘŠŤÚŮÝŽ])", candidate) if p.strip(" ,")]
        if len(split_parts) > 1:
            parts = split_parts

    if not parts:
        return authors.strip()

    uniq: List[str] = []
    seen: Set[str] = set()
    filler = {"a", "a kol", "a kol.", "kol", "kol.", "kol a"}
    for part in parts:
        norm = re.sub(r"\s+", " ", part).strip(" ,;")
        norm = re.sub(r"\s*,\s*", ", ", norm)
        lower = norm.lower()
        if re.fullmatch(r"[aA]\b", norm) or lower in filler or re.search(r"\bkol\.?\b", lower):
            continue
        norm = re.sub(r"\s+a\s+kol\.?$", "", norm, flags=re.IGNORECASE).strip(" ,;")
        if not norm:
            continue
        key = norm.lower()
        if key in seen:
            continue
        seen.add(key)
        uniq.append(norm)
    return "; ".join(uniq)


def _normalize_series_index(val: str) -> str:
    raw = (val or "").strip()
    if not raw:
        return ""
    raw = raw.replace(",", ".")
    try:
        num = float(raw)
    except ValueError:
        return ""
    if num.is_integer():
        return str(int(num))
    # Omezíme délku a odstraníme zbytečné nuly.
    text = f"{num:.3f}".rstrip("0").rstrip(".")
    return text


def _clean_metadata_fields(md: Dict[str, str]) -> Dict[str, str]:
    cleaned: Dict[str, str] = {}
    for key, val in md.items():
        if isinstance(val, str):
            cleaned[key] = val.strip()
        else:
            cleaned[key] = val
    if cleaned.get("authors"):
        cleaned["authors"] = _dedup_authors(cleaned["authors"])
    if cleaned.get("isbn"):
        cleaned["isbn"] = cleaned["isbn"].replace(" ", "").replace("-", "")
    if cleaned.get("series"):
        cleaned["series"] = re.sub(r"#\s*\d+", "", cleaned["series"]).strip(" -;")
    if "series index" in cleaned:
        normalized_idx = _normalize_series_index(cleaned.get("series index", ""))
        if normalized_idx:
            cleaned["series index"] = normalized_idx
        else:
            cleaned.pop("series index", None)
    if not cleaned.get("series"):
        cleaned.pop("series index", None)
    return cleaned


def _backfill_series_info(target: Dict[str, str], fallback: Dict[str, str]) -> Dict[str, str]:
    merged = target.copy()
    fb_idx = (fallback.get("series index") or "").strip()
    if fb_idx and not merged.get("series index"):
        merged["series index"] = fb_idx
    fb_series = (fallback.get("series") or "").strip()
    fb_lang = (fallback.get("language") or "").lower()
    if fb_series and not merged.get("series") and fb_lang.startswith("cs"):
        merged["series"] = fb_series
    return merged

def _find_detail_url(node) -> Optional[str]:
    if not node:
        return None
    # Hledejte odkaz přímo na uzlu i vnořeně, aby se zachytily různě strukturované výsledky.
    href = None
    if getattr(node, "name", "") == "a" and node.get("href"):
        href = node.get("href")
    if not href and hasattr(node, "find"):
        link = node.find("a", href=re.compile(r"/(book|kniha|knihy|prehled-knihy)/"))
        if link and link.get("href"):
            href = link.get("href")
    if href:
        return urllib.parse.urljoin("https://www.databazeknih.cz", href)
    return None


def fetch_from_databazeknih_by_isbn(isbn: str) -> Dict[str, str]:
    if not WEBLIBS_AVAILABLE or not isbn:
        return {}
    try:
        q = urllib.parse.quote_plus(isbn)
        url = f"https://www.databazeknih.cz/search?q={q}"
        headers = {"User-Agent": "Mozilla/5.0 (compatible; epub-studio/1.0)"}
        resp = requests.get(url, headers=headers, timeout=WEB_TIMEOUT)
        if resp.status_code != 200:
            return {}
        soup = BeautifulSoup(resp.text, "html.parser")
        candidate = None
        selectors = [".book-list-item", ".bok", ".book-info", ".search-result", ".book"]
        for selector in selectors:
            node = soup.select_one(selector)
            if node:
                candidate = node
                break
        if candidate is None:
            detail_url = _find_detail_url(soup)
            if detail_url:
                return _fetch_databazeknih_detail(detail_url)
        if candidate:
            return _extract_from_candidate(candidate)
        return {}
    except (requests.RequestException, Exception):
        return {}

def fetch_databazeknih_candidates_by_title(title: str, limit: int = 12) -> List[Dict[str, str]]:
    if not WEBLIBS_AVAILABLE or not title:
        return []
    try:
        q = urllib.parse.quote_plus(title)
        url = f"https://www.databazeknih.cz/search?q={q}"
        headers = {"User-Agent": "Mozilla/5.0 (compatible; epub-studio/1.0)"}
        resp = requests.get(url, headers=headers, timeout=WEB_TIMEOUT)
        if resp.status_code != 200:
            return []
        soup = BeautifulSoup(resp.text, "html.parser")
        selectors = ["p.new", ".book-list-item", ".bok", ".search-result", ".book"]
        seen: Set[str] = set()
        results: List[Dict[str, str]] = []
        nodes: List = []
        for selector in selectors:
            nodes.extend(soup.select(selector))
        if not nodes:
            nodes = soup.find_all("a", href=re.compile(r"/(book|kniha|knihy|prehled-knihy)/"))
        for node in nodes:
            meta = _extract_from_candidate(node)
            detail_url = _find_detail_url(node)
            if detail_url:
                meta.setdefault("detail_url", detail_url)
            if not meta.get("title") and detail_url:
                detail_data = _fetch_databazeknih_detail(detail_url)
                for key in ("title", "authors", "series", "series index", "isbn"):
                    if detail_data.get(key) and key not in meta:
                        meta[key] = detail_data[key]
            meta = _clean_metadata_fields(meta)
            if not meta.get("title"):
                continue
            key = f"{meta.get('title','')}|{meta.get('authors','')}|{meta.get('detail_url','')}"
            if key in seen:
                continue
            seen.add(key)
            results.append(meta)
            if len(results) >= limit:
                break
        return results
    except (requests.RequestException, Exception):
        return []

def _fetch_databazeknih_detail(detail_url: str) -> Dict[str, str]:
    if not WEBLIBS_AVAILABLE:
        return {}
    try:
        headers = {"User-Agent": "Mozilla/5.0 (compatible; epub-studio/1.0)"}
        resp = requests.get(detail_url, headers=headers, timeout=WEB_TIMEOUT)
        if resp.status_code != 200:
            return {}
        soup = BeautifulSoup(resp.text, "html.parser")
        def _clean_dbk_title(raw: str) -> str:
            raw = raw or ""
            junk = [
                "Číst",
                "Chci si koupit",
                "Nedočtené",
                "Čtenářská výzva",
                "Vytvořit vlastní seznam",
                "Koupit",
                "Koupit eknihu",
                "Antikvariát",
            ]
            for token in junk:
                raw = re.sub(rf"\b{re.escape(token)}\b", " ", raw, flags=re.IGNORECASE)
            raw = re.sub(r"\s+\|\s*Datab[aá]ze\s*knih.*$", "", raw, flags=re.IGNORECASE)
            raw = re.sub(r"[#]{1,2}\s*\d+", " ", raw)
            raw = re.sub(r"\s+", " ", raw).strip(" -\u2013\u2014")
            if " - " in raw:
                parts = [p.strip(" -") for p in raw.split(" - ") if p.strip(" -")]
                if len(parts) >= 2:
                    preferred = next((p for p in parts if not re.search(r"#\d", p)), parts[0])
                    raw = preferred
            return raw

        title_candidates: List[str] = []
        og_title = soup.find("meta", attrs={"property": "og:title"})
        if og_title and og_title.get("content"):
            title_candidates.append(_clean_dbk_title(og_title["content"]))
        title_node = soup.find("h1")
        if title_node:
            title_candidates.append(_clean_dbk_title(title_node.get_text(" ", strip=True)))
        title = next((t for t in title_candidates if t), "")
        text_full = soup.get_text(" ", strip=True)
        author = ""
        author_links = soup.find_all("a", href=re.compile(r"/(autor|autori)/"))
        if author_links:
            authors = [a.get_text(strip=True) for a in author_links if a.get_text(strip=True)]
            author = "; ".join(authors)
        else:
            match = re.search(r"Autor(?:\:)?\s*([A-ZŽŠČŘÉÚŮÓÁ][^\n\r,]{2,100})", text_full)
            if match:
                author = match.group(1).strip()
        series = ""
        series_index = ""
        series_block = soup.find(class_=re.compile("orangeBoxSmall"))
        if series_block:
            series_link = series_block.find("a", href=re.compile(r"/serie/"))
            if series_link and series_link.get_text(strip=True):
                series = series_link.get_text(strip=True)
            idx_span = series_block.find("span", string=re.compile(r"\d+\.\s*d[ií]l", re.IGNORECASE))
            if idx_span:
                match_idx = re.search(r"(\d+)", idx_span.get_text(strip=True))
                if match_idx:
                    series_index = match_idx.group(1)
        if not series:
            series_patterns = [
                r"(?P<series>[^<>\n]{3,120}?)\s*série\s*<\s*(?P<idx>\d+)\.\s*díl\s*>",
                r"(?P<series>[^<>\n]{3,120}?)\s*ser[ií]e\s*<\s*(?P<idx>\d+)\.\s*d[ií]l\s*>",
                r"(?P<series>.+?)\s*\((?P<idx>\d+)\.\s*d[ií]l\)",
            ]
            for pattern in series_patterns:
                match = re.search(pattern, text_full, flags=re.IGNORECASE)
                if match:
                    series = match.group("series").strip()
                    series_index = match.group("idx").strip()
                    break
        if not series and not series_index:
            series_link = soup.find("a", href=re.compile(r"/serie/"))
            if series_link and series_link.get_text(strip=True):
                series = series_link.get_text(strip=True)
                ctx_nodes = [series_link.parent, series_link.find_next("span", string=re.compile(r"\d+\.\s*d[ií]l", re.IGNORECASE))]
                for ctx in ctx_nodes:
                    text_ctx = ctx.get_text(" ", strip=True) if hasattr(ctx, "get_text") else ""
                    idx_match = re.search(r"(\d+)\.\s*d[ií]l", text_ctx, flags=re.IGNORECASE)
                    if idx_match:
                        series_index = idx_match.group(1).strip()
                        break

        isbn = ""
        isbn_nodes = []
        isbn_nodes.extend(soup.find_all(attrs={"itemprop": re.compile("isbn", re.IGNORECASE)}))
        isbn_nodes.extend(soup.find_all("meta", attrs={"property": re.compile("isbn", re.IGNORECASE)}))
        for label in soup.find_all(["dt", "th"], string=re.compile("ISBN", re.IGNORECASE)):
            sib = label.find_next_sibling(["dd", "td"])
            if sib:
                isbn_nodes.append(sib)
        if not isbn_nodes:
            isbn_match = re.search(r"ISBN(?:\s*13)?[:\s]+([0-9\-\s]{10,17})", text_full, flags=re.IGNORECASE)
            isbn = isbn_match.group(1) if isbn_match else ""
        else:
            for node in isbn_nodes:
                cand = node.get("content", "") if hasattr(node, "get") else ""
                if not cand:
                    cand = node.get_text(" ", strip=True)
                match = re.search(r"([0-9\-\s]{10,17})", cand)
                if match:
                    isbn = match.group(1)
                    break
        result = {}
        if title:
            result["title"] = title
        if author:
            result["authors"] = author
        if series:
            result["series"] = series
        if series_index:
            result["series index"] = series_index
        if isbn:
            result["isbn"] = isbn
        return result
    except (requests.RequestException, Exception):
        return {}

def _extract_from_candidate(candidate) -> Dict[str, str]:
    title = ""
    author = ""
    year = ""
    classes = candidate.get("class", []) if hasattr(candidate, "get") else []
    if isinstance(classes, str):
        classes = [classes]
    if "new" in classes:
        title_link = candidate.find("a", class_=re.compile("new"))
        if title_link:
            title = title_link.get_text(strip=True)
        note = candidate.find(class_=re.compile("pozn"))
        if note:
            text_note = note.get_text(" ", strip=True)
            match = re.search(r"(\d{4}),\s*(.+)", text_note)
            if match:
                year = match.group(1)
                author = match.group(2).strip()
            elif text_note:
                author = text_note
    if not title:
        title_node = candidate.find(["h3", "h2", "h1"])
        if title_node:
            title = title_node.get_text(strip=True)
    if not author:
        author_selectors = [".autor", ".author", ".book-author", ".authors", ".book-info .autor", ".book-info .authors"]
        for selector in author_selectors:
            node = candidate.select_one(selector)
            if node and node.get_text(strip=True):
                author = node.get_text(strip=True)
                break
    if not author:
        author_link = candidate.find("a", href=re.compile(r"/author/"))
        if author_link:
            author = author_link.get_text(strip=True)
    result = {}
    if title:
        result["title"] = title
    if author:
        result["authors"] = author
    if year:
        result["year"] = year
    return result

def open_databazeknih(isbn: str, title: str) -> None:
    query = isbn if isbn.strip() else title
    q = urllib.parse.quote_plus(query)
    webbrowser.open(f"https://www.databazeknih.cz/search?q={q}")

class UiSignals(QtCore.QObject):
    log = QtCore.Signal(str)
    progress = QtCore.Signal(int, int)
    metadata_ready = QtCore.Signal(object)
    busy = QtCore.Signal(bool, str)


class MainWindow(QtWidgets.QMainWindow):
    def __init__(self) -> None:
        super().__init__()
        self.setWindowTitle(f"{APP_TITLE} v{APP_VERSION}")
        self.resize(1250, 820)
        self.setAcceptDrops(True)
        self._dbk_dialog_open = False
        self._metadata_busy = False
        self._files: list[Path] = []
        self._current_path: Path | None = None
        self.signals = UiSignals()
        self.signals.log.connect(self._append_log)
        self.signals.progress.connect(self._set_progress)
        self.signals.metadata_ready.connect(self._apply_metadata_from_signal)
        self.signals.busy.connect(self._set_busy)
        self._build_ui()
        self._apply_theme()
        self._check_dependencies()

    def _apply_theme(self) -> None:
        self.setStyleSheet(
            f"""
            QMainWindow{{background:{COLOR_BG}; color:{COLOR_TEXT};}}
            QWidget{{color:{COLOR_TEXT};}}
            QFrame{{background:{COLOR_BLOCK};}}
            QListWidget{{background:{COLOR_INPUT}; border:1px solid {COLOR_PANEL};}}
            QTextEdit{{background:{COLOR_INPUT}; border:1px solid {COLOR_PANEL};}}
            QLineEdit{{background:{COLOR_INPUT}; border:1px solid {COLOR_PANEL}; padding:6px;}}
            QSpinBox{{background:{COLOR_INPUT}; border:1px solid {COLOR_PANEL}; padding:4px;}}
            QPushButton{{background:{COLOR_PANEL}; border:1px solid {COLOR_PANEL}; padding:6px 10px;}}
            QPushButton:hover{{background:{COLOR_ACCENT};}}
            QCheckBox{{spacing:8px;}}
            QProgressBar{{background:{COLOR_INPUT}; border:1px solid {COLOR_PANEL}; text-align:center;}}
            QProgressBar::chunk{{background:{COLOR_ACCENT};}}
            """
        )

    def _build_ui(self) -> None:
        central = QtWidgets.QWidget()
        self.setCentralWidget(central)
        root = QtWidgets.QHBoxLayout(central)
        root.setContentsMargins(12, 12, 12, 12)
        root.setSpacing(12)

        left_panel = QtWidgets.QFrame()
        left_layout = QtWidgets.QVBoxLayout(left_panel)
        left_layout.setSpacing(10)

        self.drop_label = QtWidgets.QLabel("Přetáhni soubory nebo složku sem")
        self.drop_label.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
        self.drop_label.setMinimumHeight(90)
        self.drop_label.setStyleSheet(f"background:{COLOR_INPUT}; border:1px dashed {COLOR_PANEL};")
        left_layout.addWidget(self.drop_label)

        files_row = QtWidgets.QHBoxLayout()
        self.add_files_btn = QtWidgets.QPushButton("Přidat soubory")
        self.add_folder_btn = QtWidgets.QPushButton("Přidat složku")
        files_row.addWidget(self.add_files_btn)
        files_row.addWidget(self.add_folder_btn)
        left_layout.addLayout(files_row)

        self.files_list = QtWidgets.QListWidget()
        self.files_list.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.SingleSelection)
        left_layout.addWidget(self.files_list, 1)

        batch_row = QtWidgets.QHBoxLayout()
        self.convert_selected_btn = QtWidgets.QPushButton("Převést vybraný")
        self.convert_all_btn = QtWidgets.QPushButton("Převést vše")
        batch_row.addWidget(self.convert_selected_btn)
        batch_row.addWidget(self.convert_all_btn)
        left_layout.addLayout(batch_row)

        root.addWidget(left_panel, 2)

        right_panel = QtWidgets.QFrame()
        right_layout = QtWidgets.QVBoxLayout(right_panel)
        right_layout.setSpacing(10)

        header = QtWidgets.QLabel(f"Profil čištění: {CLEAN_PROFILE}")
        right_layout.addWidget(header)

        flags_row = QtWidgets.QHBoxLayout()
        self.auto_pipeline = QtWidgets.QCheckBox("Auto doplnění po dropu")
        flags_row.addWidget(self.auto_pipeline)
        right_layout.addLayout(flags_row)

        threads_row = QtWidgets.QHBoxLayout()
        threads_row.addWidget(QtWidgets.QLabel("Lehká vlákna"))
        self.light_threads = QtWidgets.QSpinBox()
        self.light_threads.setRange(1, 32)
        self.light_threads.setValue(DEFAULT_LIGHT)
        threads_row.addWidget(self.light_threads)
        threads_row.addWidget(QtWidgets.QLabel("Těžká vlákna"))
        self.heavy_threads = QtWidgets.QSpinBox()
        self.heavy_threads.setRange(1, 32)
        self.heavy_threads.setValue(DEFAULT_HEAVY)
        threads_row.addWidget(self.heavy_threads)
        right_layout.addLayout(threads_row)

        form = QtWidgets.QFormLayout()
        self.title_edit = QtWidgets.QLineEdit()
        self.authors_edit = QtWidgets.QLineEdit()
        self.series_edit = QtWidgets.QLineEdit()
        self.series_index_edit = QtWidgets.QLineEdit()
        self.language_edit = QtWidgets.QLineEdit()
        self.tags_edit = QtWidgets.QLineEdit()
        self.isbn_edit = QtWidgets.QLineEdit()
        form.addRow("Název", self.title_edit)
        form.addRow("Autoři", self.authors_edit)
        form.addRow("Série", self.series_edit)
        form.addRow("Pořadí v sérii", self.series_index_edit)
        form.addRow("Jazyk", self.language_edit)
        form.addRow("Štítky", self.tags_edit)
        form.addRow("ISBN", self.isbn_edit)
        right_layout.addLayout(form)

        action_row = QtWidgets.QHBoxLayout()
        self.auto_meta_btn = QtWidgets.QPushButton("Najít metadata")
        self.save_meta_btn = QtWidgets.QPushButton("Uložit metadata")
        self.rename_btn = QtWidgets.QPushButton("Přejmenovat")
        action_row.addWidget(self.auto_meta_btn)
        action_row.addWidget(self.save_meta_btn)
        action_row.addWidget(self.rename_btn)
        right_layout.addLayout(action_row)

        action_row2 = QtWidgets.QHBoxLayout()
        self.analyze_btn = QtWidgets.QPushButton("Analyzovat EPUB")
        self.open_dbk_btn = QtWidgets.QPushButton("Otevřít DatabazeKnih")
        action_row2.addWidget(self.analyze_btn)
        action_row2.addWidget(self.open_dbk_btn)
        right_layout.addLayout(action_row2)

        self.progress_label = QtWidgets.QLabel("Průběh: 0/0")
        self.progress_bar = QtWidgets.QProgressBar()
        right_layout.addWidget(self.progress_label)
        right_layout.addWidget(self.progress_bar)

        self.busy_label = QtWidgets.QLabel("")
        self.busy_label.setStyleSheet(f"color:{COLOR_ACCENT};")
        self.busy_spinner = QtWidgets.QProgressBar()
        self.busy_spinner.setTextVisible(False)
        self.busy_spinner.setRange(0, 1)
        self.busy_spinner.hide()
        self.busy_label.hide()
        right_layout.addWidget(self.busy_label)
        right_layout.addWidget(self.busy_spinner)

        self.log = QtWidgets.QTextEdit()
        self.log.setReadOnly(True)
        right_layout.addWidget(self.log, 1)

        root.addWidget(right_panel, 3)

        self.add_files_btn.clicked.connect(self._add_files)
        self.add_folder_btn.clicked.connect(self._add_folder)
        self.files_list.currentItemChanged.connect(self._on_file_selected)
        self.convert_selected_btn.clicked.connect(self._convert_selected)
        self.convert_all_btn.clicked.connect(self._convert_all)
        self.auto_meta_btn.clicked.connect(self._smart_metadata_pipeline)
        self.save_meta_btn.clicked.connect(self._save_metadata)
        self.rename_btn.clicked.connect(self._rename_by_metadata)
        self.analyze_btn.clicked.connect(self._analyze_current_epub)
        self.open_dbk_btn.clicked.connect(self._open_databazeknih)

    def _append_log(self, msg: str) -> None:
        self.log.append(msg)

    def _log(self, msg: str) -> None:
        if threading.current_thread() is threading.main_thread():
            self._append_log(msg)
        else:
            self.signals.log.emit(msg)

    def _set_progress(self, done: int, total: int) -> None:
        total_safe = total or 1
        self.progress_label.setText(f"Průběh: {done}/{total}")
        self.progress_bar.setValue(int(min(done / total_safe, 1.0) * 100))

    def _set_busy(self, active: bool, text: str) -> None:
        if active:
            self.busy_label.setText(text)
            self.busy_label.show()
            self.busy_spinner.setRange(0, 0)
            self.busy_spinner.show()
        else:
            self.busy_label.hide()
            self.busy_spinner.hide()

    def _apply_metadata_from_signal(self, md: dict[str, str]) -> None:
        self._fill_metadata_fields(md)

    def _check_dependencies(self) -> None:
        missing_tools = []
        for cmd in ("ebook-convert", "ebook-meta", "fetch-ebook-metadata"):
            if not which(cmd):
                missing_tools.append(cmd)
        if missing_tools:
            self._log(f"VAROVANI: Chybi nastroje: {', '.join(missing_tools)}")
            self._log("Nainstaluj Calibre: https://calibre-ebook.com/")
        if not WEBLIBS_AVAILABLE:
            self._log("VAROVANI: requests/beautifulsoup4 nejsou nainstalovany.")
            self._log("Automaticke doplnovani z DatabazeKnih nebude funkcni.")
            self._log("Nainstaluj: pip install requests beautifulsoup4")
        if not SEND2TRASH_AVAILABLE:
            self._log("INFO: send2trash neni nainstalovany (mazani mimo kos)")
        self._log("Pripraveno.")

    def _add_paths(self, paths: list[Path]) -> None:
        added = 0
        first_added: Path | None = None
        for path in paths:
            if path.is_dir():
                for file in find_books(path):
                    if file not in self._files:
                        self._files.append(file)
                        self.files_list.addItem(str(file))
                        added += 1
                        if not first_added:
                            first_added = file
            elif is_supported(path):
                if path not in self._files:
                    self._files.append(path)
                    self.files_list.addItem(str(path))
                    added += 1
                    if not first_added:
                        first_added = path
        if added:
            self._log(f"Přidáno souborů: {added}")
            if first_added:
                items = self.files_list.findItems(str(first_added), QtCore.Qt.MatchFlag.MatchExactly)
                if items:
                    self.files_list.setCurrentItem(items[0])
        else:
            self._log("Nenalezeny podporované soubory.")

    def _add_files(self) -> None:
        paths, _ = QtWidgets.QFileDialog.getOpenFileNames(
            self,
            "Vyber soubory",
            "",
            "Knihy (*.epub *.mobi *.azw3 *.pdf *.doc *.docx)",
        )
        self._add_paths([Path(p) for p in paths])

    def _add_folder(self) -> None:
        folder = QtWidgets.QFileDialog.getExistingDirectory(self, "Vyber složku")
        if folder:
            self._add_paths([Path(folder)])

    def dragEnterEvent(self, event: QtGui.QDragEnterEvent) -> None:
        if event.mimeData().hasUrls():
            event.acceptProposedAction()
            self.drop_label.setStyleSheet(f"background:{COLOR_PANEL}; border:1px dashed {COLOR_ACCENT};")

    def dragLeaveEvent(self, event: QtGui.QDragLeaveEvent) -> None:
        self.drop_label.setStyleSheet(f"background:{COLOR_INPUT}; border:1px dashed {COLOR_PANEL};")
        super().dragLeaveEvent(event)

    def dropEvent(self, event: QtGui.QDropEvent) -> None:
        self.drop_label.setStyleSheet(f"background:{COLOR_INPUT}; border:1px dashed {COLOR_PANEL};")
        paths = [Path(url.toLocalFile()) for url in event.mimeData().urls()]
        self._add_paths(paths)

    def _on_file_selected(self, current: QtWidgets.QListWidgetItem, previous: QtWidgets.QListWidgetItem) -> None:
        if not current:
            return
        path = Path(current.text())
        self._current_path = path
        self._autoload_metadata(path)
        if self.auto_pipeline.isChecked():
            self._smart_metadata_pipeline()

    def _autoload_metadata(self, path: Path) -> None:
        if not which("ebook-meta"):
            self._log("ebook-meta není v PATH.")
            return
        self.signals.busy.emit(True, "Načítám metadata…")
        md = read_metadata(path)
        md = self._merge_guess(md, path)
        self._fill_metadata_fields(md)
        self.signals.busy.emit(False, "")
        self._log(f"Metadata načtena z: {path.name}")

    def _fill_metadata_fields(self, md: dict[str, str]) -> None:
        cleaned = _clean_metadata_fields(md)
        self.title_edit.setText(cleaned.get("title", ""))
        self.authors_edit.setText(cleaned.get("authors", ""))
        self.series_edit.setText(cleaned.get("series", ""))
        self.series_index_edit.setText(cleaned.get("series index", ""))
        self.language_edit.setText(cleaned.get("language", ""))
        self.tags_edit.setText(cleaned.get("tags", ""))
        self.isbn_edit.setText(cleaned.get("isbn", ""))

    def _collect_metadata(self) -> dict[str, str]:
        return _clean_metadata_fields(
            {
                "title": self.title_edit.text(),
                "authors": self.authors_edit.text(),
                "series": self.series_edit.text(),
                "series index": self.series_index_edit.text(),
                "language": self.language_edit.text(),
                "tags": self.tags_edit.text(),
                "isbn": self.isbn_edit.text(),
            }
        )

    def _merge_guess(self, md: dict[str, str], path: Path) -> dict[str, str]:
        guessed = guess_metadata_from_filename(path)
        for key, val in guessed.items():
            if key not in md or not str(md[key]).strip():
                md[key] = val
        if not md.get("language"):
            md["language"] = "cs"
        return md

    def _build_title_candidates(self, path: Path, md: dict[str, str]) -> list[str]:
        candidates: list[str] = []
        base_title = md.get("title", "").strip() or path.stem
        series = md.get("series", "").strip()
        series_idx = md.get("series index", "").strip()
        if base_title:
            candidates.append(base_title)
        if series:
            if series_idx:
                candidates.append(f"{series_idx}. v sérii {series}")
                candidates.append(f"{series} {series_idx}")
            candidates.append(series)
        seen: set[str] = set()
        ordered: list[str] = []
        for cand in candidates:
            if cand and cand not in seen:
                ordered.append(cand)
                seen.add(cand)
        return ordered

    def _save_metadata(self) -> None:
        path = self._current_path
        if not path or not path.exists():
            self._log("Soubor neexistuje.")
            return
        md = self._collect_metadata()
        ok = write_metadata(path, md)
        self._log("Metadata uložena." if ok else "Chyba při ukládání metadat (viz _error.txt).")

    def _choose_databazeknih_candidate(self, candidates: list[dict[str, str]]) -> dict[str, str] | None:
        if not candidates:
            return None
        if len(candidates) == 1:
            return candidates[0]
        if self._dbk_dialog_open:
            return None
        self._dbk_dialog_open = True
        try:
            dialog = QtWidgets.QDialog(self)
            dialog.setWindowTitle("Vyber knihu (DatabazeKnih)")
            dialog.resize(880, 420)
            dialog.setWindowModality(QtCore.Qt.WindowModality.ApplicationModal)
            layout = QtWidgets.QVBoxLayout(dialog)
            layout.addWidget(QtWidgets.QLabel("Vyber správný titul a autora:"))
            list_widget = QtWidgets.QListWidget()
            list_widget.setWordWrap(True)
            for cand in candidates:
                title = cand.get("title", "Bez názvu")
                author = cand.get("authors", "Bez autora")
                year = cand.get("year", "")
                header = f"{title}" + (f" ({year})" if year else "")
                list_widget.addItem(f"{header} — {author}")
            row_h = list_widget.sizeHintForRow(0) or 24
            visible_rows = min(5, list_widget.count())
            list_widget.setMinimumHeight(row_h * visible_rows + 16)
            if list_widget.count():
                list_widget.setCurrentRow(0)
            layout.addWidget(list_widget)
            buttons = QtWidgets.QDialogButtonBox(QtWidgets.QDialogButtonBox.StandardButton.Ok | QtWidgets.QDialogButtonBox.StandardButton.Cancel)
            layout.addWidget(buttons)
            buttons.accepted.connect(dialog.accept)
            buttons.rejected.connect(dialog.reject)
            dialog.raise_()
            dialog.activateWindow()
            if dialog.exec() == QtWidgets.QDialog.DialogCode.Accepted and list_widget.currentRow() >= 0:
                return candidates[list_widget.currentRow()]
            return None
        finally:
            self._dbk_dialog_open = False

    def _choose_databazeknih_candidate_safe(self, candidates: list[dict[str, str]]) -> dict[str, str] | None:
        return self._run_on_main_thread(lambda: self._choose_databazeknih_candidate(candidates))

    def _show_metadata_proposal_dialog(self, original: dict[str, str], proposed: dict[str, str]) -> bool:
        dialog = QtWidgets.QDialog(self)
        dialog.setWindowTitle("Návrh metadat")
        layout = QtWidgets.QVBoxLayout(dialog)
        grid = QtWidgets.QFormLayout()
        fields = [
            ("Název", "title"),
            ("Autoři", "authors"),
            ("Série", "series"),
            ("Pořadí v sérii", "series index"),
            ("Jazyk", "language"),
            ("Štítky", "tags"),
            ("ISBN", "isbn"),
        ]
        for label, key in fields:
            curr = original.get(key, "")
            prop = proposed.get(key, "")
            text = f"Návrh: {prop or '—'}"
            if curr and curr != prop:
                text = f"{text}\nPůvodně: {curr}"
            grid.addRow(label, QtWidgets.QLabel(text))
        layout.addLayout(grid)
        buttons = QtWidgets.QDialogButtonBox(QtWidgets.QDialogButtonBox.StandardButton.Ok | QtWidgets.QDialogButtonBox.StandardButton.Cancel)
        layout.addWidget(buttons)
        buttons.accepted.connect(dialog.accept)
        buttons.rejected.connect(dialog.reject)
        return dialog.exec() == QtWidgets.QDialog.DialogCode.Accepted

    def _run_on_main_thread(self, fn) -> object:
        if threading.current_thread() is threading.main_thread():
            return fn()
        result: dict[str, object] = {}
        done = threading.Event()

        def wrapper() -> None:
            try:
                result["value"] = fn()
            finally:
                done.set()

        QtCore.QTimer.singleShot(0, wrapper)
        if not done.wait(timeout=60):
            self._log("VAROVANI: Čekání na UI dialog vypršelo.")
        return result.get("value")

    def _smart_metadata_pipeline(self) -> None:
        path = self._current_path
        if not path or not path.exists():
            self._log("Soubor neexistuje.")
            return
        if not WEBLIBS_AVAILABLE:
            self._log("DatabazeKnih není dostupná (chybí requests/bs4).")
            return
        if self._metadata_busy:
            self._log("Vyhledávání metadat již běží.")
            return
        self._metadata_busy = True

        def job() -> None:
            self.signals.busy.emit(True, "Hledám metadata…")
            try:
                base_md: dict[str, str] = read_metadata(path) if which("ebook-meta") else {}
                base_md = self._merge_guess(base_md, path)
                base_md = _clean_metadata_fields(base_md)
                candidates = self._build_title_candidates(path, base_md)
                isbn = (base_md.get("isbn") or "").strip()
                fetched: dict[str, str] = {}
                if isbn:
                    self._log(f"Hledám ISBN {isbn}…")
                    primary = fetch_from_databazeknih_by_isbn(isbn)
                    fetched = _clean_metadata_fields(primary or {})
                if not fetched:
                    for title_option in candidates:
                        if not title_option:
                            continue
                        self._log(f"Hledám název: {title_option}")
                        candidates_md = fetch_databazeknih_candidates_by_title(title_option, limit=5)
                        if candidates_md:
                            choice_md = self._choose_databazeknih_candidate_safe(candidates_md)
                            if not choice_md:
                                self._log("Výběr kandidáta byl zrušen.")
                                return
                            detail_url = choice_md.get("detail_url")
                            if detail_url:
                                details = _fetch_databazeknih_detail(detail_url)
                                if details:
                                    fetched.update(details)
                            if not fetched:
                                fetched.update({k: v for k, v in choice_md.items() if k != "detail_url"})
                        if fetched:
                            break
                merged = base_md.copy()
                fetched_clean = _clean_metadata_fields(fetched)
                for key, val in fetched_clean.items():
                    if val:
                        merged[key] = val
                merged = _backfill_series_info(merged, fetched_clean)
                if not merged.get("language"):
                    merged["language"] = "cs"
                if not merged.get("tags"):
                    merged["tags"] = self.tags_edit.text()
                if isbn and not merged.get("isbn"):
                    merged["isbn"] = isbn
                merged = _clean_metadata_fields(merged)
                if not merged:
                    self._log("Nic k doplnění, zůstal původní obsah.")
                    return
                approved = bool(self._run_on_main_thread(lambda: self._show_metadata_proposal_dialog(base_md, merged)))
                if not approved:
                    self._log("Návrh metadat byl odmítnut.")
                    return
                self.signals.metadata_ready.emit(merged)
                saved = write_metadata(path, merged)
                if saved:
                    self._log("Metadata byla uložena po potvrzení.")
                else:
                    self._log("Zápis metadat se nezdařil (viz _error.txt).")
                self._run_on_main_thread(lambda: self._rename_by_metadata(merged))
            finally:
                self.signals.busy.emit(False, "")
                self._metadata_busy = False

        threading.Thread(target=job, daemon=True).start()

    def _analyze_current_epub(self) -> None:
        path = self._current_path
        if not path or not path.exists():
            self._log("Soubor neexistuje.")
            return
        if path.suffix.lower() != ".epub":
            self._log("Analýza funguje jen pro EPUB. Nejprve převeď soubor.")
            return
        self.signals.busy.emit(True, "Analyzuji EPUB…")
        analysis = analyze_epub_structure(path)
        summary = generate_change_summary(analysis)
        preview = apply_epub_fixes(path, analysis, dry_run=True)
        dialog = QtWidgets.QDialog(self)
        dialog.setWindowTitle("Analýza EPUB")
        layout = QtWidgets.QVBoxLayout(dialog)
        layout.addWidget(QtWidgets.QLabel(summary))
        extra = [
            f"K odstranění: {len(preview.get('deleted', []))}",
            f"K očištění: {len(preview.get('cleaned', []))}",
            f"Bez zásahu: {len(preview.get('kept', []))}",
        ]
        layout.addWidget(QtWidgets.QLabel("\n".join(extra)))
        buttons = QtWidgets.QDialogButtonBox()
        apply_btn = buttons.addButton("Provést opravy", QtWidgets.QDialogButtonBox.ButtonRole.AcceptRole)
        cancel_btn = buttons.addButton("Zrušit", QtWidgets.QDialogButtonBox.ButtonRole.RejectRole)
        layout.addWidget(buttons)

        def do_apply() -> None:
            dialog.accept()
            result = apply_epub_fixes(path, analysis, dry_run=False)
            if result.get("backup"):
                self._log(f"Vytvořena záloha: {result['backup']}")
            self._log(
                f"Opravy EPUB: odstraněno {len(result.get('deleted', []))}, čištěno {len(result.get('cleaned', []))}, ponecháno {len(result.get('kept', []))}."
            )
            for note in result.get("report", []):
                self._log(note)
            if result.get("errors"):
                for err in result["errors"]:
                    self._log(f"Chyba: {err}")
            else:
                QtWidgets.QMessageBox.information(self, "Opravy EPUB", "Opravy byly dokončeny.")

        apply_btn.clicked.connect(do_apply)
        cancel_btn.clicked.connect(dialog.reject)
        dialog.exec()
        self.signals.busy.emit(False, "")

    def _rename_by_metadata(self, md_override: dict[str, str] | None = None) -> None:
        path = self._current_path
        if not path or not path.exists():
            self._log("Soubor neexistuje.")
            return
        md = md_override or {
            "title": self.title_edit.text(),
            "authors": self.authors_edit.text(),
            "series": self.series_edit.text(),
            "series index": self.series_index_edit.text(),
        }
        name = build_filename_from_md(md)
        if not name:
            self._log("Chybí Název pro přejmenování.")
            return
        target = path.with_name(name + path.suffix)
        if target.exists():
            self._log(f"Soubor již existuje: {target.name} (nepřejmenováno).")
            return
        try:
            path.rename(target)
            self._current_path = target
            self._update_list_item(path, target)
            self._log(f"Přejmenováno: {path.name} → {target.name}")
        except OSError as exc:
            self._log(f"Chyba přejmenování: {exc}")

    def _update_list_item(self, old: Path, new: Path) -> None:
        for idx, item in enumerate(self._files):
            if item == old:
                self._files[idx] = new
                self.files_list.item(idx).setText(str(new))
                break

    def _open_databazeknih(self) -> None:
        open_databazeknih(self.isbn_edit.text(), self.title_edit.text())

    def _convert_selected(self) -> None:
        path = self._current_path
        if not path or not path.exists() or not is_supported(path):
            self._log("Vyber platný soubor.")
            return
        if not which("ebook-convert"):
            self._log("ebook-convert není v PATH.")
            return
        self.signals.progress.emit(0, 1)
        self.signals.busy.emit(True, "Převádím soubor…")

        def job() -> None:
            ok, output, msg = convert_one(path)
            if ok:
                self._log(f"OK: {output}")
            else:
                self._log(f"CHYBA: {path.name} – {msg}")
            self.signals.progress.emit(1, 1)
            self.signals.busy.emit(False, "")

        threading.Thread(target=job, daemon=True).start()

    def _convert_all(self) -> None:
        if not self._files:
            self._log("Seznam souborů je prázdný.")
            return
        if not which("ebook-convert"):
            self._log("ebook-convert není v PATH.")
            return
        try:
            light_raw = max(1, int(self.light_threads.value()))
            heavy_raw = max(1, int(self.heavy_threads.value()))
        except ValueError:
            self._log("Neplatný počet vláken.")
            return
        light_n, heavy_n = self._pick_thread_counts(light_raw, heavy_raw)
        light = [f for f in self._files if f.suffix.lower() in LIGHT_EXT]
        heavy = [f for f in self._files if f.suffix.lower() in HEAVY_EXT]
        total = len(self._files)
        self.signals.progress.emit(0, total)
        self.signals.busy.emit(True, "Probíhá dávkový převod…")
        self._log(f"Dávka: lehké={len(light)} těžké={len(heavy)} (vlákna {light_n}/{heavy_n})")

        def worker(file: Path) -> Tuple[Path, bool, Optional[Path], str]:
            ok, output, msg = convert_one(file)
            return (file, ok, output, msg)

        def run_conversion() -> None:
            results = []
            with ThreadPoolExecutor(max_workers=light_n) as ex_light, ThreadPoolExecutor(max_workers=heavy_n) as ex_heavy:
                futures = []
                for f in light:
                    futures.append(ex_light.submit(worker, f))
                for f in heavy:
                    futures.append(ex_heavy.submit(worker, f))
                done = 0
                for future in as_completed(futures):
                    file, ok, output, msg = future.result()
                    if ok:
                        self._log(f"OK: {file.name} → {Path(output).name}")
                    else:
                        self._log(f"CHYBA: {file.name} – {msg}")
                    done += 1
                    self.signals.progress.emit(done, total)
                    results.append((ok, file, msg))
            ok_count = sum(1 for x in results if x[0])
            err_count = len(results) - ok_count
            self._log(f"Hotovo. Úspěšně: {ok_count}, Chyby: {err_count}.")
            self.signals.progress.emit(total, total)
            self.signals.busy.emit(False, "")

        threading.Thread(target=run_conversion, daemon=True).start()

    def _pick_thread_counts(self, light_requested: int, heavy_requested: int) -> Tuple[int, int]:
        cores = os.cpu_count() or 12
        reserve = min(max(1, THREAD_RESERVE), max(1, cores // 3))
        budget = max(1, cores - reserve)
        light = min(light_requested, budget)
        heavy_limit = max(1, budget // 2)
        heavy = min(heavy_requested, heavy_limit)
        return max(1, light), max(1, heavy)


def main() -> None:
    missing = []
    for cmd in ("ebook-convert", "ebook-meta", "fetch-ebook-metadata"):
        if not which(cmd):
            missing.append(cmd)
    if missing:
        print(f"VAROVANI: Chybi nastroje: {', '.join(missing)}", file=sys.stderr)
        print("Nainstaluj Calibre: https://calibre-ebook.com/", file=sys.stderr)
    if not WEBLIBS_AVAILABLE:
        print("VAROVANI: Doporuceno nainstalovat: pip install requests beautifulsoup4", file=sys.stderr)
    app = QtWidgets.QApplication(sys.argv)
    window = MainWindow()
    window.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
