#!/usr/bin/env python3
"""
Test suite for Lean project, build pipeline, LaTeX conversion, cleanup, and HTTP server.
"""

import os
import sys
import threading
import time
import unittest
from http.server import HTTPServer
from pathlib import Path
from urllib.error import HTTPError
from urllib.request import Request, urlopen

# Ensure project root is on sys.path
PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

import clean_up
import lean_tools
import serve


class TestProjectConfiguration(unittest.TestCase):
    """Test project configuration files."""

    def test_lean_toolchain(self):
        toolchain_file = PROJECT_ROOT / "lean-toolchain"
        self.assertTrue(toolchain_file.exists(), "lean-toolchain must exist")
        content = toolchain_file.read_text(encoding="utf-8").strip()
        self.assertIn("leanprover/lean4:", content)

    def test_lakefile_toml(self):
        lakefile = PROJECT_ROOT / "lakefile.toml"
        self.assertTrue(lakefile.exists(), "lakefile.toml must exist")
        content = lakefile.read_text(encoding="utf-8")
        self.assertIn('name = "example"', content)
        self.assertIn('defaultTargets = ["Example"]', content)
        self.assertIn('autoImplicit = false', content)

    def test_github_workflow_exists(self):
        workflow = PROJECT_ROOT / ".github" / "workflows" / "build.yml"
        self.assertTrue(workflow.exists(), "GitHub Actions workflow must exist")
        content = workflow.read_text(encoding="utf-8")
        self.assertIn("leanprover/lean-action", content)
        self.assertIn("lake build", content)
        self.assertIn("output/", content)


class TestLeanCompilation(unittest.TestCase):
    """Test compilation with Lake and Lean CLI."""

    def test_lake_build(self):
        success = lean_tools.compile_lean(verbose=False)
        self.assertTrue(success, "Lake build should succeed with code 0")

    def test_compile_single_file(self):
        basic_lean = PROJECT_ROOT / "Example" / "Basic.lean"
        success = lean_tools.compile_lean(file_path=basic_lean, verbose=False)
        self.assertTrue(success, f"Direct compilation of {basic_lean.name} should succeed")


class TestLatexConversion(unittest.TestCase):
    """Test Lean script to LaTeX translation and output directory isolation."""

    def setUp(self):
        self.sample_lean = '''/-!
# Sample Module

This is a **bold** comment with inline `code` and math $x + y$.
-/

namespace Sample

/-- The greeting function. -/
def hello : String := "Hello!"

/-- Commutativity theorem. -/
theorem add_comm (n m : Nat) : n + m = m + n := by
  omega

end Sample
'''

    def test_markdown_to_latex_conversion(self):
        latex = lean_tools.lean_to_latex(self.sample_lean, title="Sample Test", standalone=True)
        # Check sectioning
        self.assertIn(r"\section*{Sample Module}", latex)
        # Check bold formatting
        self.assertIn(r"\textbf{bold}", latex)
        # Check inline code formatting
        self.assertIn(r"\texttt{code}", latex)
        # Check doc boxes
        self.assertIn(r"\begin{leandocbox}", latex)
        self.assertIn("The greeting function.", latex)
        # Check code listings
        self.assertIn(r"\begin{lstlisting}[language=Lean4]", latex)
        self.assertIn("theorem add_comm (n m : Nat)", latex)

    def test_file_export_to_output_dir(self):
        # By default, files must be placed in output/
        out_path = lean_tools.convert_file_to_latex(
            PROJECT_ROOT / "Example" / "Basic.lean",
            standalone=True,
            compile_pdf=False
        )
        self.assertTrue(out_path.exists())
        self.assertEqual(out_path.parent.name, "output")
        self.assertEqual(out_path.name, "Basic.tex")
        content = out_path.read_text(encoding="utf-8")
        self.assertIn(r"\section*{Example.Basic}", content)
        self.assertIn("nat_add_comm", content)


class TestCleanUpScript(unittest.TestCase):
    """Test clean_up.py functionality and safety guards."""

    def test_protected_files(self):
        self.assertTrue(clean_up.is_protected(PROJECT_ROOT / "Example" / "Basic.lean"))
        self.assertTrue(clean_up.is_protected(PROJECT_ROOT / "lakefile.toml"))
        self.assertTrue(clean_up.is_protected(PROJECT_ROOT / "lean_tools.py"))
        self.assertTrue(clean_up.is_protected(PROJECT_ROOT / ".github" / "workflows" / "build.yml"))
        self.assertFalse(clean_up.is_protected(PROJECT_ROOT / "output" / "Basic.tex"))
        self.assertFalse(clean_up.is_protected(PROJECT_ROOT / "output"))

    def test_cleanup_latex_only(self):
        # Create a dummy generated file in output/
        test_out = PROJECT_ROOT / "output" / "dummy_test.aux"
        test_out.parent.mkdir(parents=True, exist_ok=True)
        test_out.write_text("dummy aux content", encoding="utf-8")
        self.assertTrue(test_out.exists())

        # Run clean_up with latex only and quiet
        clean_up.clean_project(clean_latex=True, clean_lake=False, clean_pycache=False, quiet=True)
        self.assertFalse(test_out.exists())
        # Ensure source code remains intact
        self.assertTrue((PROJECT_ROOT / "Example" / "Basic.lean").exists())


class TestServeHandler(unittest.TestCase):
    """Test HTTP server routes and custom request handler."""

    @classmethod
    def setUpClass(cls):
        cls.server = HTTPServer(("127.0.0.1", 0), serve.CustomHTTPRequestHandler)
        cls.port = cls.server.server_port
        cls.thread = threading.Thread(target=cls.server.serve_forever, daemon=True)
        cls.thread.start()
        time.sleep(0.1)

    @classmethod
    def tearDownClass(cls):
        cls.server.shutdown()
        cls.server.server_close()

    def test_favicon_204(self):
        req = Request(f"http://127.0.0.1:{self.port}/favicon.ico")
        with urlopen(req) as resp:
            self.assertEqual(resp.status, 204)

    def test_root_redirect_and_dashboard(self):
        req = Request(f"http://127.0.0.1:{self.port}/")
        with urlopen(req) as resp:
            self.assertEqual(resp.status, 200)
            self.assertIn("/example/", resp.geturl())
            body = resp.read().decode("utf-8")
            self.assertIn("Lean 4 Project Dashboard", body)
            self.assertIn("Example.lean", body)

    def test_serve_lean_source_file(self):
        req = Request(f"http://127.0.0.1:{self.port}/example/Example/Basic.lean")
        with urlopen(req) as resp:
            self.assertEqual(resp.status, 200)
            body = resp.read().decode("utf-8")
            self.assertIn("def hello", body)
            self.assertIn("nat_add_comm", body)


if __name__ == "__main__":
    unittest.main()
