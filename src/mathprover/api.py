from .lean_runner import LeanResult, check_lean
from .proof_search import ProofResult, prove


def certify(lean_source: str) -> LeanResult:
    """Certify a complete Lean theorem and proof."""
    return check_lean(lean_source)