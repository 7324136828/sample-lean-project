#!/usr/bin/env python3
"""
HTTP server for the Lean project, based on skill/example2/serve.py.

Serves project documentation, formalization views, generated LaTeX, and PDF files.

Usage:
    python serve.py [port]
    # Example: python serve.py 8080
"""

import argparse
import html
import os
import sys
from http import HTTPStatus
from http.server import HTTPServer, SimpleHTTPRequestHandler
from pathlib import Path
from urllib.parse import unquote, urlparse

# Directories to serve
ROOT_DIR = Path(__file__).resolve().parent
DOCS_SITE = ROOT_DIR / ".lake" / "build" / "doc"
SITE_DIR = ROOT_DIR / "_site"
OUTPUT_DIR = ROOT_DIR / "output"


def generate_index_html() -> str:
    """Generate a clean dashboard HTML page if no custom index.html is present."""
    # Find generated PDF and TeX files (checking output/ first)
    pdf_files = [
        p for p in ROOT_DIR.glob("**/*.pdf")
        if ".lake" not in p.parts and "skill" not in p.parts and "skills" not in p.parts
    ]
    pdf_links = "".join(
        f'<li><a href="/example/{p.relative_to(ROOT_DIR).as_posix()}" target="_blank">📄 {p.name}</a> '
        f'<span class="meta">({p.stat().st_size // 1024} KB in <code>{p.parent.name}/</code>)</span></li>'
        for p in pdf_files
    ) or "<li><em>No PDF files generated yet. Run <code>python lean_tools.py to-latex Example/Basic.lean --pdf</code></em></li>"

    tex_files = [
        t for t in ROOT_DIR.glob("**/*.tex")
        if ".lake" not in t.parts and "skill" not in t.parts and "skills" not in t.parts
    ]
    tex_links = "".join(
        f'<li><a href="/example/{t.relative_to(ROOT_DIR).as_posix()}" target="_blank">📝 {t.name}</a> '
        f'<span class="meta">(in <code>{t.parent.name}/</code>)</span></li>'
        for t in tex_files
    ) or "<li><em>No LaTeX files generated yet.</em></li>"

    lean_files = [
        l for l in ROOT_DIR.glob("**/*.lean")
        if ".lake" not in l.parts and "skill" not in l.parts and "skills" not in l.parts
    ]
    lean_links = "".join(
        f'<li><a href="/example/{l.relative_to(ROOT_DIR).as_posix()}">🔷 {l.relative_to(ROOT_DIR).as_posix()}</a></li>'
        for l in lean_files
    )

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Lean 4 Project Dashboard</title>
  <style>
    :root {{
      --primary: #2563eb;
      --bg: #f8fafc;
      --card: #ffffff;
      --text: #1e293b;
      --border: #e2e8f0;
    }}
    body {{
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
      line-height: 1.6;
      background: var(--bg);
      color: var(--text);
      margin: 0;
      padding: 2rem;
    }}
    .container {{
      max-width: 800px;
      margin: 0 auto;
    }}
    h1 {{ color: #0f172a; margin-bottom: 0.5rem; }}
    .subtitle {{ color: #64748b; margin-top: 0; margin-bottom: 2rem; }}
    .card {{
      background: var(--card);
      border-radius: 8px;
      padding: 1.5rem;
      margin-bottom: 1.5rem;
      border: 1px solid var(--border);
      box-shadow: 0 1px 3px rgba(0,0,0,0.05);
    }}
    .card h2 {{
      margin-top: 0;
      font-size: 1.25rem;
      color: #334155;
      border-bottom: 1px solid var(--border);
      padding-bottom: 0.5rem;
    }}
    ul {{ list-style: none; padding-left: 0; }}
    li {{ padding: 0.4rem 0; }}
    a {{
      color: var(--primary);
      text-decoration: none;
      font-weight: 500;
    }}
    a:hover {{ text-decoration: underline; }}
    .meta {{ font-size: 0.85rem; color: #94a3b8; margin-left: 0.5rem; }}
    code {{
      background: #e2e8f0;
      padding: 0.2rem 0.4rem;
      border-radius: 4px;
      font-size: 0.9em;
    }}
  </style>
</head>
<body>
  <div class="container">
    <h1>Lean 4 Project Dashboard</h1>
    <p class="subtitle">Minimalistic formalization and documentation viewer</p>

    <div class="card">
      <h2>Lean Source Files</h2>
      <ul>{lean_links}</ul>
    </div>

    <div class="card">
      <h2>Compiled Documents (PDF)</h2>
      <ul>{pdf_links}</ul>
    </div>

    <div class="card">
      <h2>Generated LaTeX (.tex)</h2>
      <ul>{tex_links}</ul>
    </div>
  </div>
</body>
</html>
"""


class CustomHTTPRequestHandler(SimpleHTTPRequestHandler):
    """
    Custom request handler based on skill/example2/serve.py.
    Provides route mapping, favicon handling, and index redirection.
    """

    def do_GET(self):
        if self.path == "/favicon.ico":
            self.send_response(HTTPStatus.NO_CONTENT)
            self.end_headers()
            return
        elif self.path in ("/", ""):
            self.send_response(HTTPStatus.MOVED_PERMANENTLY)
            self.send_header("Location", "/example/")
            self.end_headers()
            return
        elif self.path in ("/example", "/example/"):
            index_path = SITE_DIR / "index.html"
            if index_path.exists():
                return super().do_GET()
            content = generate_index_html().encode("utf-8")
            self.send_response(HTTPStatus.OK)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(content)))
            self.end_headers()
            self.wfile.write(content)
            return

        super().do_GET()

    def translate_path(self, path):
        parsed = urlparse(path)
        path = unquote(parsed.path)

        # Serve /example/docs/* from DOCS_SITE if it exists
        if path.startswith("/example/docs/"):
            path = path.replace("//", "/")
            rel_path = path[len("/example/docs/"):]
            return str(DOCS_SITE / rel_path)

        # Serve /example/output/* from OUTPUT_DIR
        elif path.startswith("/example/output/"):
            rel_path = path[len("/example/output/"):]
            return str(OUTPUT_DIR / rel_path)

        # Serve /example/* from ROOT_DIR
        elif path.startswith("/example/"):
            rel_path = path[len("/example/"):]
            return str(ROOT_DIR / rel_path)

        return super().translate_path(path)


def run_server(port: int = 8000, host: str = "127.0.0.1"):
    handler = CustomHTTPRequestHandler
    with HTTPServer((host, port), handler) as httpd:
        print(f"[Server] Serving at http://localhost:{port}/example/")
        print(f"[Server] Project Root: {ROOT_DIR}")
        print(f"[Server] Output Dir:   {OUTPUT_DIR}")
        print(f"[Server] Docs Site:    {DOCS_SITE}")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print("\n[Server] Shutting down cleanly.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Serve Lean project artifacts and documentation.")
    parser.add_argument(
        "port",
        default=8000,
        type=int,
        nargs="?",
        help="Port to bind to (default: 8000)"
    )
    parser.add_argument(
        "--host",
        default="127.0.0.1",
        help="Host address to bind to (default: 127.0.0.1)"
    )
    args = parser.parse_args()
    run_server(port=args.port, host=args.host)
