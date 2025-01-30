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

## Generate Python code

The Python code in `src/gen-main/python` and `src/gen-test/python` are generated from sources in Hydra's bootstrapping implementation, Hydra-Haskell.
See the [Hydra-Haskell README](https://github.com/CategoricalData/hydra/tree/main/hydra-haskell)
for more information on how this works.
You can generate Hydra-Python kernel and test code by first entering GHCi

```bash
cd ../hydra-haskell && stack ghci
```

And then running the following commands in the GHC REPL.

```haskell
writePython "../hydra-python/src/gen-main/python" (hydraCoreModule:tier0Modules)
writePython "../hydra-python/src/gen-test/python" testModules
```

This will generate `hydra/core` and the tier-0 kernel modules, as well as the test suite.
Support for generating the rest of the kernel code is currently in progress.

### Validate generated code

The generated Hydra Kernel code is in `src/gen-main/python` and `src/gen-test/python`.
From the `hydra-python` directory, you can validate this code with a command like:

```bash
find src/gen-main/ -name "*.py" -exec python3 -m py_compile {} +
find src/gen-test/ -name "*.py" -exec python3 -m py_compile {} +
```
