#!/usr/bin/env python3
"""
Lean Tools: Compile Lean 4 projects and convert Lean scripts to LaTeX.

Usage examples:
    # 1. Compile the project
    python lean_tools.py build
    python lean_tools.py build --clean

    # 2. Convert a Lean file to LaTeX (.tex) inside 'output/' directory
    python lean_tools.py to-latex Example/Basic.lean
    # -> generates output/Basic.tex

    # 3. Convert to LaTeX and compile to PDF inside 'output/' directory
    python lean_tools.py to-latex Example/Basic.lean --pdf
    # -> generates output/Basic.tex and output/Basic.pdf

    # 4. Run both build and LaTeX conversion for all Lean files into 'output/'
    python lean_tools.py all
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

# Project root and default output directory
PROJECT_ROOT = Path(__file__).resolve().parent
DEFAULT_OUTPUT_DIR = PROJECT_ROOT / "output"


# ---------------------------------------------------------------------------
# Lean Compilation
# ---------------------------------------------------------------------------

def find_executable(name: str) -> str:
    """Find executable in PATH or standard elan locations."""
    path = shutil.which(name)
    if path:
        return path

    # Common elan path on Windows
    user_profile = os.environ.get("USERPROFILE", "")
    elan_bin = Path(user_profile) / ".elan" / "bin" / f"{name}.exe"
    if elan_bin.exists():
        return str(elan_bin)

    return name


def compile_lean(
    target: str | None = None,
    clean: bool = False,
    file_path: str | Path | None = None,
    cwd: str | Path | None = None,
    verbose: bool = True
) -> bool:
    """
    Compile Lean project or a specific Lean file.

    Args:
        target: Optional Lake target name (e.g. 'Example')
        clean: If True, run 'lake clean' prior to building
        file_path: Optional path to a specific .lean file to check directly
        cwd: Working directory (defaults to project root)
        verbose: Whether to print build progress to stdout
    """
    work_dir = Path(cwd) if cwd else PROJECT_ROOT

    lake_bin = find_executable("lake")
    lean_bin = find_executable("lean")

    if clean:
        if verbose:
            print("[LeanTools] Running 'lake clean'...")
        cmd_clean = [lake_bin, "clean"]
        res_clean = subprocess.run(cmd_clean, cwd=work_dir)
        if res_clean.returncode != 0:
            print(f"[LeanTools] Warning: 'lake clean' returned code {res_clean.returncode}")

    start_time = time.time()

    if file_path:
        file_p = Path(file_path).resolve()
        if not file_p.exists():
            print(f"[LeanTools] Error: File not found: {file_p}")
            return False
        if verbose:
            print(f"[LeanTools] Compiling single Lean file: {file_p.name}...")
        cmd = [lean_bin, str(file_p)]
    else:
        if verbose:
            target_str = f" target '{target}'" if target else ""
            print(f"[LeanTools] Building Lean project{target_str} with Lake...")
        cmd = [lake_bin, "build"]
        if target:
            cmd.append(target)

    res = subprocess.run(cmd, cwd=work_dir, text=True, capture_output=True)
    duration = time.time() - start_time

    if res.stdout:
        print(res.stdout.strip())
    if res.stderr:
        print(res.stderr.strip(), file=sys.stderr)

    if res.returncode == 0:
        if verbose:
            print(f"[LeanTools] [SUCCESS] Compilation succeeded in {duration:.2f}s.")
        return True
    else:
        if verbose:
            print(f"[LeanTools] [FAILURE] Compilation failed with exit code {res.returncode} ({duration:.2f}s).", file=sys.stderr)
        return False


# ---------------------------------------------------------------------------
# Lean to LaTeX Converter
# ---------------------------------------------------------------------------

LATEX_PREAMBLE_TEMPLATE = r"""\documentclass[11pt,a4paper]{article}
\usepackage{iftex}
\ifPDFTeX
  \usepackage[utf8]{inputenc}
  \usepackage[T1]{fontenc}
\else
  \usepackage{fontspec}
\fi
\usepackage[margin=1in]{geometry}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{xcolor}
\usepackage{listings}
\usepackage{tcolorbox}
\tcbuselibrary{skins,breakable}
\usepackage{hyperref}

% Color definitions
\definecolor{leanKeyword}{RGB}{0, 51, 153}
\definecolor{leanComment}{RGB}{46, 125, 50}
\definecolor{leanString}{RGB}{186, 45, 0}
\definecolor{leanTactic}{RGB}{119, 41, 83}
\definecolor{leanBg}{RGB}{248, 250, 252}
\definecolor{leanBorder}{RGB}{203, 213, 225}
\definecolor{leanDocBg}{RGB}{241, 245, 249}
\definecolor{leanDocBorder}{RGB}{148, 163, 184}

% Lean 4 listings configuration
\lstdefinelanguage{Lean4}{
  keywords={
    def, theorem, lemma, example, axiom, inductive, structure, class, instance,
    where, by, import, open, namespace, end, have, let, match, with, if, then, else,
    noncomputable, section, variable, universe, abbrev, mutual, notation, syntax,
    macro, return, do, fun, show, from, suffices
  },
  keywordstyle=\color{leanKeyword}\bfseries,
  morekeywords=[2]{omega, rfl, simp, aesop, ring, linarith, norm_num, intro, exact, apply, cases, induction, rw, rewrite},
  keywordstyle=[2]\color{leanTactic}\bfseries,
  comment=[l]{--},
  morecomment=[s]{/-}{-/},
  commentstyle=\color{leanComment}\itshape,
  string=[b]",
  stringstyle=\color{leanString},
  basicstyle=\ttfamily\small,
  breaklines=true,
  breakatwhitespace=true,
  showstringspaces=false,
  keepspaces=true,
  columns=flexible,
  tabsize=2,
  literate=
    {ℕ}{{\ensuremath{\mathbb{N}}}}1
    {ℤ}{{\ensuremath{\mathbb{Z}}}}1
    {ℚ}{{\ensuremath{\mathbb{Q}}}}1
    {ℝ}{{\ensuremath{\mathbb{R}}}}1
    {ℂ}{{\ensuremath{\mathbb{C}}}}1
    {∀}{{\ensuremath{\forall}}}1
    {∃}{{\ensuremath{\exists}}}1
    {→}{{\ensuremath{\to}}}1
    {↔}{{\ensuremath{\leftrightarrow}}}1
    {∧}{{\ensuremath{\land}}}1
    {∨}{{\ensuremath{\lor}}}1
    {¬}{{\ensuremath{\neg}}}1
    {≤}{{\ensuremath{\le}}}1
    {≥}{{\ensuremath{\ge}}}1
    {≠}{{\ensuremath{\ne}}}1
    {∈}{{\ensuremath{\in}}}1
    {∉}{{\ensuremath{\notin}}}1
    {⊆}{{\ensuremath{\subseteq}}}1
    {∪}{{\ensuremath{\cup}}}1
    {∩}{{\ensuremath{\cap}}}1
    {∑}{{\ensuremath{\sum}}}1
    {∏}{{\ensuremath{\prod}}}1
    {×}{{\ensuremath{\times}}}1
    {⟨}{{\ensuremath{\langle}}}1
    {⟩}{{\ensuremath{\rangle}}}1
    {λ}{{\ensuremath{\lambda}}}1
    {⬝}{{\ensuremath{\cdot}}}1
    {·}{{\ensuremath{\cdot}}}1
    {∘}{{\ensuremath{\circ}}}1
    {α}{{\ensuremath{\alpha}}}1
    {β}{{\ensuremath{\beta}}}1
    {γ}{{\ensuremath{\gamma}}}1
    {δ}{{\ensuremath{\delta}}}1
    {ε}{{\ensuremath{\varepsilon}}}1
    {⊢}{{\ensuremath{\vdash}}}1
    {⊨}{{\ensuremath{\vDash}}}1
}

% Custom environments for code and documentation boxes
\newtcolorbox{leancodebox}{
  colback=leanBg,
  colframe=leanBorder,
  arc=3mm,
  boxrule=0.8pt,
  left=8pt, right=8pt, top=6pt, bottom=6pt,
  breakable
}

\newtcolorbox{leandocbox}[1][]{
  colback=leanDocBg,
  colframe=leanDocBorder,
  arc=2mm,
  boxrule=0.6pt,
  left=8pt, right=8pt, top=5pt, bottom=5pt,
  fonttitle=\bfseries\small,
  title={Documentation},
  #1
}

\title{__TITLE__}
\author{Generated by Lean Tools}
\date{\today}

\begin{document}
\maketitle

__CONTENT__

\end{document}
"""


def markdown_to_latex(text: str) -> str:
    """Convert a markdown comment block (from Lean docstring) into LaTeX."""
    lines = text.strip().splitlines()
    latex_lines = []
    in_itemize = False

    for line in lines:
        stripped = line.strip()

        # Section headers
        if stripped.startswith("### "):
            if in_itemize:
                latex_lines.append(r"\end{itemize}")
                in_itemize = False
            title = escape_latex(stripped[4:])
            latex_lines.append(rf"\subsubsection*{{{title}}}")
            continue
        elif stripped.startswith("## "):
            if in_itemize:
                latex_lines.append(r"\end{itemize}")
                in_itemize = False
            title = escape_latex(stripped[3:])
            latex_lines.append(rf"\subsection*{{{title}}}")
            continue
        elif stripped.startswith("# "):
            if in_itemize:
                latex_lines.append(r"\end{itemize}")
                in_itemize = False
            title = escape_latex(stripped[2:])
            latex_lines.append(rf"\section*{{{title}}}")
            continue

        # Bullet list items
        if stripped.startswith("- ") or stripped.startswith("* "):
            if not in_itemize:
                latex_lines.append(r"\begin{itemize}")
                in_itemize = True
            item_text = format_inline_markdown(stripped[2:])
            latex_lines.append(rf"  \item {item_text}")
            continue
        else:
            if in_itemize and stripped == "":
                latex_lines.append(r"\end{itemize}")
                in_itemize = False

        if not stripped:
            latex_lines.append("")
            continue

        latex_lines.append(format_inline_markdown(line))

    if in_itemize:
        latex_lines.append(r"\end{itemize}")

    return "\n".join(latex_lines)


def escape_latex(text: str) -> str:
    """Escape special LaTeX characters in plain text."""
    chars = {
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    pattern = re.compile("|".join(re.escape(k) for k in chars.keys()))
    return pattern.sub(lambda m: chars[m.group(0)], text)


def format_inline_markdown(text: str) -> str:
    """Handle inline markdown such as `code`, **bold**, *italic*, and $math$."""
    # Temporarily preserve math $...$
    math_segments = []
    def save_math(match):
        math_segments.append(match.group(0))
        return f"__MATH_{len(math_segments)-1}__"

    text_no_math = re.sub(r"\$[^$]+\$", save_math, text)

    # Inline code: `code`
    def replace_code(match):
        c = match.group(1)
        c_esc = c.replace("\\", r"\textbackslash{}").replace("{", r"\{").replace("}", r"\}")
        return rf"\texttt{{{c_esc}}}"

    text_no_math = re.sub(r"`([^`]+)`", replace_code, text_no_math)

    # Bold: **bold**
    text_no_math = re.sub(r"\*\*([^*]+)\*\*", lambda m: rf"\textbf{{{escape_latex(m.group(1))}}}", text_no_math)
    # Italic: *italic*
    text_no_math = re.sub(r"\*([^*]+)\*", lambda m: rf"\textit{{{escape_latex(m.group(1))}}}", text_no_math)

    # Escape remaining text outside math/commands
    tokens = re.split(r"(__MATH_\d+__|\\texttt\{[^}]*\}|\\textbf\{[^}]*\}|\\textit\{[^}]*\})", text_no_math)
    escaped_tokens = []
    for token in tokens:
        if token.startswith("__MATH_") or token.startswith(r"\texttt") or token.startswith(r"\textbf") or token.startswith(r"\textit"):
            escaped_tokens.append(token)
        else:
            escaped_tokens.append(escape_latex(token))
    res = "".join(escaped_tokens)

    # Restore math
    for idx, math_str in enumerate(math_segments):
        res = res.replace(f"__MATH_{idx}__", math_str)

    return res


def lean_to_latex(
    lean_source: str,
    title: str = "Lean 4 Formalization",
    standalone: bool = True
) -> str:
    """
    Parse Lean 4 source code and convert to structured LaTeX.

    Segments code into:
    - Module docstrings (/-! ... -/) -> Markdown-to-LaTeX sections/prose
    - Declaration docstrings (/-- ... -/) -> Highlighted doc boxes
    - Lean code -> Styled lstlisting blocks
    """
    doc_pattern = re.compile(
        r"(/\-!(.*?)\-/)|(/\-\-(.*?)\-/)|(/\*(.*?)\*/)",
        re.DOTALL
    )

    chunks = []
    last_idx = 0

    for match in doc_pattern.finditer(lean_source):
        start, end = match.span()
        code_before = lean_source[last_idx:start]
        if code_before.strip():
            chunks.append(("code", code_before.strip()))

        full_match = match.group(0)
        if full_match.startswith("/-!"):
            # Module doc
            content = match.group(2)
            chunks.append(("module_doc", content))
        elif full_match.startswith("/--"):
            # Declaration doc
            content = match.group(4)
            chunks.append(("decl_doc", content))
        last_idx = end

    remaining_code = lean_source[last_idx:]
    if remaining_code.strip():
        chunks.append(("code", remaining_code.strip()))

    body_parts = []

    for kind, content in chunks:
        if kind == "module_doc":
            body_parts.append(markdown_to_latex(content))
            body_parts.append("")
        elif kind == "decl_doc":
            doc_latex = markdown_to_latex(content)
            body_parts.append(r"\begin{leandocbox}")
            body_parts.append(doc_latex)
            body_parts.append(r"\end{leandocbox}")
        elif kind == "code":
            body_parts.append(r"\begin{leancodebox}")
            body_parts.append(r"\begin{lstlisting}[language=Lean4]")
            body_parts.append(content)
            body_parts.append(r"\end{lstlisting}")
            body_parts.append(r"\end{leancodebox}")
            body_parts.append("")

    content_str = "\n".join(body_parts)

    if standalone:
        latex_doc = LATEX_PREAMBLE_TEMPLATE.replace("__TITLE__", escape_latex(title))
        latex_doc = latex_doc.replace("__CONTENT__", content_str)
        return latex_doc
    else:
        return content_str


def convert_file_to_latex(
    input_file: str | Path,
    output_file: str | Path | None = None,
    output_dir: str | Path | None = None,
    standalone: bool = True,
    compile_pdf: bool = False,
    engine: str = "xelatex",
    clean_aux: bool = True
) -> Path:
    """
    Convert a single .lean file to a .tex file exclusively inside the output directory,
    and optionally compile to PDF.
    """
    in_path = Path(input_file).resolve()
    if not in_path.exists():
        raise FileNotFoundError(f"Lean file not found: {in_path}")

    # Ensure output directory exists
    out_dir = Path(output_dir).resolve() if output_dir else DEFAULT_OUTPUT_DIR
    out_dir.mkdir(parents=True, exist_ok=True)

    # Determine final output .tex path inside the output directory
    if output_file:
        out_p = Path(output_file)
        if out_p.is_absolute():
            out_path = out_p
        elif len(out_p.parts) > 1:
            out_path = PROJECT_ROOT / out_p
        else:
            out_path = out_dir / out_p.name
    else:
        out_path = out_dir / f"{in_path.stem}.tex"

    out_path.parent.mkdir(parents=True, exist_ok=True)

    source_code = in_path.read_text(encoding="utf-8")
    title = f"{in_path.stem} (Lean 4)"

    latex_code = lean_to_latex(source_code, title=title, standalone=standalone)
    out_path.write_text(latex_code, encoding="utf-8")
    print(f"[LeanTools] Generated LaTeX: {out_path}")

    if compile_pdf and standalone:
        pdf_path = compile_latex_to_pdf(out_path, engine=engine, clean_aux=clean_aux)
        return pdf_path

    return out_path


def get_project_version() -> str:
    """Retrieve current project version from version file or lakefile.toml."""
    version_file = PROJECT_ROOT / "version"
    if version_file.exists():
        v = version_file.read_text(encoding="utf-8").strip()
        if v:
            return v
    lakefile = PROJECT_ROOT / "lakefile.toml"
    if lakefile.exists():
        match = re.search(r'version\s*=\s*"([^"]+)"', lakefile.read_text(encoding="utf-8"))
        if match:
            return f"v{match.group(1)}"
    return "v1.0.0"


def compile_latex_to_pdf(
    tex_path: Path,
    engine: str = "xelatex",
    clean_aux: bool = True
) -> Path:
    """Compile a .tex file to .pdf using xelatex or pdflatex inside the output folder."""
    compiler = find_executable(engine)
    if not compiler or not shutil.which(compiler):
        fallback = "pdflatex" if engine == "xelatex" else "xelatex"
        compiler = find_executable(fallback)
        if not compiler or not shutil.which(compiler):
            print(
                f"[LeanTools] [ERROR] Neither '{engine}' nor '{fallback}' was found in PATH.\n"
                f"            Please install TeX Live, MiKTeX, or MacTeX to compile PDFs.",
                file=sys.stderr
            )
            return tex_path

    print(f"[LeanTools] Compiling LaTeX to PDF in {tex_path.parent.name}/ with {Path(compiler).name}...")
    cmd = [compiler, "-interaction=nonstopmode", tex_path.name]
    try:
        res = subprocess.run(cmd, cwd=tex_path.parent, capture_output=True, text=True)
    except OSError as e:
        print(f"[LeanTools] [ERROR] Could not run compiler '{compiler}': {e}", file=sys.stderr)
        return tex_path

    pdf_file = tex_path.with_suffix(".pdf")
    if pdf_file.exists():
        print(f"[LeanTools] [SUCCESS] Generated PDF: {pdf_file}")

        # Clean up compiler auxiliary files to keep output/ pristine
        if clean_aux:
            aux_exts = [".aux", ".log", ".out", ".toc", ".fls", ".fdb_latexmk", ".synctex.gz"]
            for ext in aux_exts:
                aux_file = tex_path.with_suffix(ext)
                if aux_file.exists():
                    try:
                        aux_file.unlink()
                    except OSError:
                        pass
        return pdf_file
    else:
        print(f"[LeanTools] [ERROR] LaTeX compilation failed. Log output:", file=sys.stderr)
        log_lines = res.stdout.splitlines()[-25:]
        for line in log_lines:
            print("  ", line, file=sys.stderr)
        return tex_path


# ---------------------------------------------------------------------------
# Main CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Lean Tools: Build Lean 4 projects and convert Lean scripts to LaTeX."
    )
    parser.add_argument(
        "-v", "--version",
        action="version",
        version=f"%(prog)s {get_project_version()}",
        help="Show project version and exit",
    )
    subparsers = parser.add_subparsers(dest="command", help="Command to execute")

    # Build command
    build_parser = subparsers.add_parser("build", help="Compile Lean project with Lake or Lean")
    build_parser.add_argument("--clean", action="store_true", help="Run 'lake clean' prior to building")
    build_parser.add_argument("--target", type=str, default=None, help="Target library or executable to build")
    build_parser.add_argument("--file", type=str, default=None, help="Compile a specific .lean file directly")

    # To-LaTeX command
    latex_parser = subparsers.add_parser("to-latex", help="Convert Lean file to LaTeX (.tex) and optional PDF in output/")
    latex_parser.add_argument("input", type=str, help="Path to input .lean file or directory")
    latex_parser.add_argument("-o", "--output", type=str, default=None, help="Output .tex filename or path")
    latex_parser.add_argument("-d", "--output-dir", type=str, default=str(DEFAULT_OUTPUT_DIR), help="Output directory (default: 'output')")
    latex_parser.add_argument("--pdf", action="store_true", help="Compile the generated .tex to .pdf")
    latex_parser.add_argument("--snippet", action="store_true", help="Generate snippet only (no document preamble)")
    latex_parser.add_argument("--engine", type=str, default="xelatex", choices=["xelatex", "pdflatex", "lualatex"], help="LaTeX engine to compile PDF")
    latex_parser.add_argument("--keep-aux", action="store_true", help="Keep auxiliary LaTeX build files (.aux, .log, .out)")

    # All command
    all_parser = subparsers.add_parser("all", help="Build project and convert all .lean files to LaTeX and PDF in output/")
    all_parser.add_argument("-d", "--output-dir", type=str, default=str(DEFAULT_OUTPUT_DIR), help="Output directory (default: 'output')")
    all_parser.add_argument("--pdf", action="store_true", default=True, help="Also generate PDF files")

    # Optional shorthand flags on root
    parser.add_argument("--build", action="store_true", help="Shortcut to run build")
    parser.add_argument("--to-latex", type=str, default=None, help="Shortcut to convert file to LaTeX")

    args = parser.parse_args()

    if args.build:
        compile_lean()
        return
    if args.to_latex:
        convert_file_to_latex(args.to_latex, standalone=True, compile_pdf=False)
        return

    if args.command == "build":
        success = compile_lean(target=args.target, clean=args.clean, file_path=args.file)
        sys.exit(0 if success else 1)

    elif args.command == "to-latex":
        in_path = Path(args.input)
        out_dir = Path(args.output_dir)
        pdf_ok = True
        if in_path.is_file():
            out_result = convert_file_to_latex(
                in_path,
                output_file=args.output,
                output_dir=out_dir,
                standalone=not args.snippet,
                compile_pdf=args.pdf,
                engine=args.engine,
                clean_aux=not args.keep_aux
            )
            if args.pdf and out_result.suffix != ".pdf":
                pdf_ok = False
        elif in_path.is_dir():
            lean_files = [f for f in in_path.rglob("*.lean") if ".lake" not in f.parts and "skill" not in f.parts]
            print(f"[LeanTools] Found {len(lean_files)} Lean files in {in_path}:")
            for lf in lean_files:
                out_result = convert_file_to_latex(
                    lf,
                    output_dir=out_dir,
                    standalone=not args.snippet,
                    compile_pdf=args.pdf,
                    engine=args.engine,
                    clean_aux=not args.keep_aux
                )
                if args.pdf and out_result.suffix != ".pdf":
                    pdf_ok = False
        else:
            print(f"[LeanTools] Error: Path not found: {in_path}", file=sys.stderr)
            sys.exit(1)

        if args.pdf and not pdf_ok:
            print("[LeanTools] Error: PDF compilation failed.", file=sys.stderr)
            sys.exit(1)

    elif args.command == "all":
        print("=== Step 1: Compiling Lean Project ===")
        ok = compile_lean()
        if not ok:
            print("[LeanTools] Compilation failed; aborting.", file=sys.stderr)
            sys.exit(1)

        print(f"\n=== Step 2: Converting Lean Scripts to LaTeX & PDF in '{args.output_dir}' ===")
        out_dir = Path(args.output_dir)
        lean_files = [
            f for f in PROJECT_ROOT.rglob("*.lean")
            if ".lake" not in f.parts and "skill" not in f.parts
        ]
        all_pdf_ok = True
        for lf in lean_files:
            out_result = convert_file_to_latex(lf, output_dir=out_dir, compile_pdf=args.pdf)
            if args.pdf and out_result.suffix != ".pdf":
                all_pdf_ok = False

        if args.pdf and not all_pdf_ok:
            print("[LeanTools] Error: One or more PDF compilations failed.", file=sys.stderr)
            sys.exit(1)

        print(f"\n[LeanTools] All done! Outputs generated in {out_dir}")

    else:
        parser.print_help()


if __name__ == "__main__":
    main()
