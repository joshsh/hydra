"""A module for tier-0 constants."""

from __future__ import annotations
import hydra.core

ignoredVariable = "_"

# A placeholder name for row types as they are being constructed.
placeholderName = hydra.core.Name("Placeholder")

maxTraceDepth = 50