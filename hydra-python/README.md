# Hydra-Python

This directory contains a Python implementation of Hydra, still in progress.

## Validate generated Python code

The generated Hydra Kernel code is in `src/gen-main/python`.
From the Hydra root directory, you can validate this code with a command like:

```bash
find hydra-python/src/gen-main/ -name "*.py" -exec python3 -m py_compile {} +
```
