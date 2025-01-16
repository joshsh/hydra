# Hydra-Python

This directory contains a Python implementation of Hydra, still in progress.

## Getting Started

Install uv.
```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
```

Make the python virtual environment.
```bash
uv venv --python 3.12
source .venv/bin/activate
```

Install the dependencies.
```bash
uv sync
```

## Formatting, Linting, and Type Checking

All of these commands can run from the Hydra Python root directory, but files/directories can be specified as arguments
as well to get more specific results.

#### Formatting
Format the code.
```bash
ruff format
```

#### Linting
Run the linter.
Run the linter.
```bash
ruff check
```
Fix the linting errors in the code if they are fixable (e.g. removing unused imports).
```bash
ruff check --fix
```

#### Static Type Checking
Run the type checker.
```bash
pyright
```

## Validate generated Python code

The generated Hydra Kernel code is in `src/gen-main/python`.
From the Hydra root directory, you can validate this code with a command like:

```bash
find hydra-python/src/gen-main/ -name "*.py" -exec python3 -m py_compile {} +
```
