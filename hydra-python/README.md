# Hydra-Python

This directory contains a Python implementation of Hydra, still in progress.

## Getting Started

Install uv with the following command,
```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
```

Make the python virtual environment,
```bash
uv venv --python 3.12
source .venv/bin/activate
```

Install the dependencies,
```bash
uv sync
```

## Validate generated Python code

The generated Hydra Kernel code is in `src/gen-main/python`.
From the Hydra root directory, you can validate this code with a command like:

```bash
find hydra-python/src/gen-main/ -name "*.py" -exec python3 -m py_compile {} +
```
