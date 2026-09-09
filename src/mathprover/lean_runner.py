from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import subprocess
import tempfile


PROJECT_ROOT = Path(__file__).resolve().parents[2]
LEAN_PROJECT = PROJECT_ROOT / "lean_project"


@dataclass
class LeanResult:
    certified: bool
    stdout: str
    stderr: str
    source: str


def check_lean(source: str) -> LeanResult:
    """Ask Lean to certify a complete Lean source string."""
    with tempfile.NamedTemporaryFile(
        mode="w",
        suffix=".lean",
        dir=LEAN_PROJECT,
        encoding="utf-8",
        delete=False,
    ) as file:
        file.write(source)
        lean_file = Path(file.name)

    try:
        completed = subprocess.run(
            ["lake", "env", "lean", lean_file.name],
            cwd=LEAN_PROJECT,
            text=True,
            capture_output=True,
            timeout=60,
        )
        return LeanResult(
            certified=completed.returncode == 0,
            stdout=completed.stdout,
            stderr=completed.stderr,
            source=source,
        )
    finally:
        lean_file.unlink(missing_ok=True)