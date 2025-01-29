import subprocess

from pytest import Session


def pytest_sessionstart(session: Session):
    """Install the package before running tests"""
    subprocess.run(["uv", "build"], check=True)
    subprocess.run(
        ["uv", "pip", "install", "dist/hydra-0.9.0-py3-none-any.whl"], check=True
    )
