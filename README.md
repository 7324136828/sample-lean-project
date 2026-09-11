# Example Lean 4 Project

A minimalistic Lean 4 project set up based on the conventions and toolchains in `skills/lean_example` and `skill/example2`.

## Structure

- `lean-toolchain`: Pinned to `leanprover/lean4:v4.34.0-rc2`.
- `lakefile.toml`: Package configuration in Lake TOML format.
- `Example.lean`: Root library entry point.
- `Example/Basic.lean`: Sample theorems and definitions with complete proofs.
- `Example/Test.lean`: Lean unit tests and verified test assertions.
- `tests/test_project.py`: Python unit test suite covering Lake compilation, LaTeX translation, cleanup, and server routing.
- `.github/workflows/build.yml`: CI workflow based on `skill/example2` with Lean action and Lake caching.
- `serve.py`: HTTP development server based on `skill/example2/serve.py` with dashboard, PDF/LaTeX serving, and route translation.
- `lean_tools.py`: Python CLI tool to compile Lean and convert Lean scripts to LaTeX / PDF exclusively in the `output/` folder.
- `clean_up.py`: Python cleanup script to purge generated files (`output/`, `.lake`, `.tex`, `.pdf`, pycache).
- `formalization.yaml`: Formalization metadata tracking the theorems and verification status.

## Building & Testing

### Building with Lake
```sh
lake build
```

### Running Test Suite
```sh
# Run Python and Lean verification test suite
python -m unittest discover -s tests -p "test_*.py" -v
```

### Compiling with `lean_tools.py`
```sh
# Standard build
python lean_tools.py build

# Clean and rebuild
python lean_tools.py build --clean

# Compile a specific .lean file
python lean_tools.py build --file Example/Basic.lean
```

## Running Local HTTP Server (`serve.py`)

Run the local server to browse source files, view the interactive dashboard, and download compiled PDFs:

```sh
python serve.py [port]
# Example:
python serve.py 8000
```
Then visit [http://localhost:8000/](http://localhost:8000/) (automatically redirects to `/example/`).

## Converting Lean to LaTeX / PDF (Isolated in `output/`)

Convert any `.lean` file to a formatted LaTeX document and optionally compile to PDF. All outputs are written to the `output/` folder:

```sh
# Generate LaTeX in output/ (output/Basic.tex)
python lean_tools.py to-latex Example/Basic.lean

# Generate LaTeX and automatically compile to PDF (output/Basic.pdf)
python lean_tools.py to-latex Example/Basic.lean --pdf

# Build project and generate LaTeX + PDF for all files in output/
python lean_tools.py all
```

## Cleaning Generated Files (`clean_up.py`)

To remove all generated files (`output/`, `.lake/`, LaTeX auxiliary files, PDFs, Python cache):

```sh
# Preview what would be deleted
python clean_up.py --dry-run

# Remove all generated artifacts
python clean_up.py

# Clean only LaTeX and PDF outputs
python clean_up.py --latex

# Clean only Lake build artifacts
python clean_up.py --lake
```

## GitHub Actions Workflow

The CI workflow in `.github/workflows/build.yml`:
1. Sets up Lean 4 via `leanprover/lean-action@v1`.
2. Restores and caches `.lake` build artifacts using `actions/cache`.
3. Cleans any corrupt cached packages.
4. Builds the Lean project (`lake build`).
5. Runs the test suite (`python -m unittest discover -s tests`).
6. Generates LaTeX documents into `output/` and uploads artifacts.

## Adding Mathlib

To add Mathlib support matching `skills/lean_example`, uncomment the `[[require]]` block for `mathlib` in `lakefile.toml` and run:

```sh
lake exe cache get
lake build
```
