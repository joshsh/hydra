# Hydra-Python

This directory contains a Python implementation of Hydra, still in progress.

## Getting Started

Install [uv](https://github.com/astral-sh/uv).
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

Install [Ruff](https://github.com/astral-sh/ruff),
[pyright](https://github.com/microsoft/pyright), and
[pytest](https://docs.pytest.org/en/stable), e.g. on macOS.
```bash
brew install ruff
brew install pyright
brew install pytest
```

## Formatting, Linting, and Type Checking

All of these commands can run from the `hydra-python` root directory, but files/directories can be specified as arguments
as well to get more specific results.

#### Formatting

Format the hand-written Python code.
```bash
ruff format
```

#### Linting

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

## Testing
To run the all the tests,
```bash
pytest
```

To run a specific test,
```bash
pytest tests/test_grammar.py
```

To match a specific test,
```bash
pytest -k test_grammar
```
or
To match a specific test,
```bash
pytest -k test_math_grammar
```

Additionally, if you want to see printed outputs, you can run the tests with the `-s` flag.
```bash
pytest -s
```

## Validate generated Python code

The generated Hydra Kernel code is in `src/gen-main/python`.
From the Hydra root directory, you can validate this code with a command like:

```bash
find hydra-python/src/gen-main/ -name "*.py" -exec python3 -m py_compile {} +
```
