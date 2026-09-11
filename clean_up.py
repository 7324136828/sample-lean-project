#!/usr/bin/env python3
"""
Clean Up Script for Lean Project

Removes all generated artifacts:
- LaTeX and PDF outputs (.tex, .pdf, .aux, .log, .out, etc.)
- The 'output' directory
- Lake build artifacts (.lake)
- Python caches (__pycache__, *.pyc)

Usage:
    python clean_up.py            # Clean all generated files
    python clean_up.py --dry-run  # Preview files to delete without deleting
    python clean_up.py --latex    # Only clean LaTeX and PDF files
    python clean_up.py --lake     # Only clean Lake build artifacts
"""

import argparse
import os
import shutil
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent

# Extensions produced by LaTeX/PDF generation
LATEX_EXTENSIONS = {
    ".aux", ".log", ".out", ".toc", ".fls", ".fdb_latexmk",
    ".synctex.gz", ".pdf", ".tex"
}

# Directories that should NEVER be deleted or searched for deletion
PROTECTED_DIRS = {
    ".git", ".github", "skill", "skills"
}

# File names that are source code and must NEVER be deleted
PROTECTED_FILES = {
    "lakefile.toml", "lakefile.lean", "lake-manifest.json",
    "lean-toolchain", "formalization.yaml", "README.md",
    "CONTRIBUTING.md", "LICENSE", ".gitignore"
}


def is_protected(path: Path) -> bool:
    """Check if path is protected from deletion."""
    try:
        rel = path.relative_to(PROJECT_ROOT)
    except ValueError:
        return True

    parts = rel.parts
    # Never touch protected directories or anything inside them
    for protected in PROTECTED_DIRS:
        if protected in parts:
            return True

    # Never touch source code or configuration files
    if path.name in PROTECTED_FILES:
        return True

    # Never delete .lean or .py files
    if path.suffix in {".lean", ".py"}:
        return True

    return False


def clean_project(
    clean_latex: bool = True,
    clean_lake: bool = True,
    clean_pycache: bool = True,
    dry_run: bool = False,
    quiet: bool = False
) -> tuple[int, int, int]:
    """
    Remove generated files and directories.
    
    Returns:
        tuple of (num_files_deleted, num_dirs_deleted, bytes_freed)
    """
    files_to_delete: list[Path] = []
    dirs_to_delete: list[Path] = []
    bytes_freed = 0

    # 1. Output directory
    output_dir = PROJECT_ROOT / "output"
    if clean_latex and output_dir.exists() and not is_protected(output_dir):
        dirs_to_delete.append(output_dir)

    # 2. Lake build directory
    lake_dir = PROJECT_ROOT / ".lake"
    if clean_lake and lake_dir.exists() and not is_protected(lake_dir):
        dirs_to_delete.append(lake_dir)

    # 3. Find stray LaTeX/PDF files outside output_dir
    if clean_latex:
        for p in PROJECT_ROOT.rglob("*"):
            if p.is_file() and not is_protected(p):
                # Don't duplicate if parent dir is already in dirs_to_delete
                if any(d in p.parents for d in dirs_to_delete):
                    continue
                if p.suffix.lower() in LATEX_EXTENSIONS:
                    files_to_delete.append(p)

    # 4. Python bytecode & cache
    if clean_pycache:
        for p in PROJECT_ROOT.rglob("__pycache__"):
            if p.is_dir() and not is_protected(p):
                dirs_to_delete.append(p)
        for p in PROJECT_ROOT.rglob("*.py[co]"):
            if p.is_file() and not is_protected(p):
                if not any(d in p.parents for d in dirs_to_delete):
                    files_to_delete.append(p)

    # Calculate sizes
    for f in files_to_delete:
        try:
            bytes_freed += f.stat().st_size
        except OSError:
            pass

    for d in dirs_to_delete:
        try:
            for item in d.rglob("*"):
                if item.is_file():
                    bytes_freed += item.stat().st_size
        except OSError:
            pass

    # Print actions
    if not quiet:
        prefix = "[DryRun] Would delete:" if dry_run else "[CleanUp] Deleting:"
        for d in dirs_to_delete:
            print(f"{prefix} (dir)  {d.relative_to(PROJECT_ROOT)}")
        for f in files_to_delete:
            print(f"{prefix} (file) {f.relative_to(PROJECT_ROOT)}")

    # Execute deletion
    if not dry_run:
        for f in files_to_delete:
            try:
                f.unlink(missing_ok=True)
            except OSError as e:
                print(f"[CleanUp] Error deleting file {f}: {e}", file=sys.stderr)

        for d in dirs_to_delete:
            try:
                shutil.rmtree(d, ignore_errors=True)
            except OSError as e:
                print(f"[CleanUp] Error deleting dir {d}: {e}", file=sys.stderr)

    kb_freed = bytes_freed / 1024.0
    action_str = "Would remove" if dry_run else "Removed"
    if not quiet:
        print(f"\n[CleanUp] {action_str} {len(files_to_delete)} files and {len(dirs_to_delete)} directories ({kb_freed:.1f} KB freed).")

    return len(files_to_delete), len(dirs_to_delete), bytes_freed


def main():
    parser = argparse.ArgumentParser(
        description="Clean generated files (.lake, LaTeX, PDF, pycache) from the Lean project."
    )
    parser.add_argument(
        "--dry-run", "-n",
        action="store_true",
        help="List files that would be removed without actually deleting them"
    )
    parser.add_argument(
        "--latex",
        action="store_true",
        help="Only clean LaTeX and PDF files and the output/ directory"
    )
    parser.add_argument(
        "--lake",
        action="store_true",
        help="Only clean Lake build artifacts (.lake)"
    )
    parser.add_argument(
        "--pycache",
        action="store_true",
        help="Only clean Python caches"
    )
    parser.add_argument(
        "--quiet", "-q",
        action="store_true",
        help="Suppress detailed listing and only print summary"
    )

    args = parser.parse_args()

    # Determine what to clean
    has_specific = args.latex or args.lake or args.pycache
    clean_latex = args.latex or not has_specific
    clean_lake = args.lake or not has_specific
    clean_pycache = args.pycache or not has_specific

    clean_project(
        clean_latex=clean_latex,
        clean_lake=clean_lake,
        clean_pycache=clean_pycache,
        dry_run=args.dry_run,
        quiet=args.quiet
    )


if __name__ == "__main__":
    main()

