from __future__ import annotations

from dataclasses import dataclass
import os

from dotenv import load_dotenv
from openai import OpenAI

from .lean_runner import LeanResult, check_lean


@dataclass
class ProofResult:
    certified: bool
    proof: str | None
    lean_result: LeanResult
    attempts: int


def _clean_proof(text: str) -> str:
    """Remove accidental Markdown fencing from a model response."""
    text = text.strip()
    if text.startswith("```"):
        lines = text.splitlines()
        text = "\n".join(lines[1:-1])
    return text.strip()


def prove(
    theorem_statement: str,
    *,
    model: str = "gpt-5",
    max_attempts: int = 3,
) -> ProofResult:
    """
    Generate and Lean-certify a proof.

    theorem_statement must include `theorem ... : ...`, but not `:= by`.
    """
    load_dotenv()

    if not os.environ.get("OPENAI_API_KEY"):
        raise RuntimeError("OPENAI_API_KEY is missing. Add it to MathProver/.env.")

    client = OpenAI()
    feedback = ""

    for attempt in range(1, max_attempts + 1):
        prompt = f"""
Write a Lean 4 proof for the theorem below.

Return only Lean code beginning with `by`.
Do not use `sorry`, `admit`, Markdown fences, or explanation.
Mathlib is imported.

Theorem:
{theorem_statement}
{feedback}
""".strip()

        response = client.responses.create(
            model=model,
            input=prompt,
        )
        proof = _clean_proof(response.output_text)

        source = f"""
import Mathlib

{theorem_statement} := {proof}
""".strip()

        lean_result = check_lean(source)

        if lean_result.certified:
            return ProofResult(
                certified=True,
                proof=proof,
                lean_result=lean_result,
                attempts=attempt,
            )

        feedback = f"""
Lean rejected the preceding proof. Correct it using this diagnostic:

{lean_result.stderr[-4000:]}
"""

    return ProofResult(
        certified=False,
        proof=None,
        lean_result=lean_result,
        attempts=max_attempts,
    )