"""Search for a Lean 4 proof of a theorem and certify it with the Lean kernel.

    from .prover import prove

    result = prove("theorem two_le_four : 2 ≤ 4", verbose=1)
    if result.certified:
        print(result.source)

`prove` takes a theorem statement without its `:= by`, searches for a tactic
script that closes the goal, and returns a `ProofResult`. `certified` is true
only if Lean accepted the proof and the finished declaration depends on nothing
beyond Mathlib's standard axioms.

The search runs in four stages:

  1. Tactic ladder. A single compile tries sixteen standard Mathlib tactics in
     a `first | ...` block, then a bisection identifies which one worked. Many
     elementary goals are closed here without any model call.

  2. Lemma grounding. The model proposes Mathlib declaration names for the
     goal, and Lean `#check`s all of them in one compile. Names that do not
     exist are recorded and excluded from every later prompt, so the repair
     loop does not spend attempts rediscovering them one at a time.

  3. Sampled generation. Each round requests several independent candidates in
     parallel via structured outputs, compiles them, and feeds the rejected
     scripts back with Lean's diagnostics attached. Sampling explores distinct
     proof strategies; the feedback loop refines a strategy that was nearly
     right.

  4. Verification. Candidates using `sorry`, `admit`, `stop`, or
     `native_decide` are rejected before compiling, since Lean accepts them
     with only a warning. A `#print axioms` trailer then confirms the proof
     rests on nothing but `propext`, `Classical.choice`, and `Quot.sound`.

Requires `OPENAI_API_KEY` in the environment or a local `.env`, a Lean
toolchain with Mathlib available to `lean_runner.check_lean`, and enough
patience for a few compiles per attempt.
"""

from __future__ import annotations

import concurrent.futures
import os
import re
import textwrap
from dataclasses import dataclass, field
from typing import Optional

from dotenv import load_dotenv
from openai import OpenAI
from pydantic import BaseModel, Field

from .lean_runner import LeanResult, check_lean

# --------------------------------------------------------------------------
# configuration
# --------------------------------------------------------------------------

MAX_HEARTBEATS = 1_000_000

# Tried in a single compile before any API call. Cheapest first; multi-tactic
# branches are parenthesised because `first` takes one tactic per alternative.
LADDER: tuple[str, ...] = (
    "rfl",
    "trivial",
    "ring",
    "omega",
    "decide",
    "norm_num",
    "simp",
    "simp_all",
    "positivity",
    "linarith",
    "nlinarith",
    "tauto",
    "aesop",
    "(constructor <;> simp_all)",
    "(field_simp; ring)",
    "exact?",
)

# Escape hatches Lean will happily accept that do not constitute a proof.
_CHEATS = re.compile(r"(?<![\w.])(sorry|sorryAx|admit|native_decide|stop)(?![\w.])")

_SAFE_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

_ERROR_HEAD = re.compile(r"^(?:.*?:\d+:\d+:\s*)?(?:error|warning):", re.MULTILINE)
# Lean quotes names with '...', `...` or Unicode quotes depending on version,
# and capitalises the message in newer releases.
_UNKNOWN_NAME = re.compile(
    r"[Uu]nknown (?:identifier|constant)\s*[`'\u2018]([^`'\u2019]+)[`'\u2019]"
)
_DECL_NAME = re.compile(r"\b(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_.'!?₀-₉]*)")
_LEAN_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_.'!?₀-₉]*$")

SYSTEM_PROMPT = """\
You are an expert Lean 4 theorem prover working with current Mathlib.

Rules:
1. `tactics_code` contains ONLY the tactic script that follows `:= by`.
   Do not include the theorem statement, `:=`, `by`, Markdown fences, or prose.
2. Never use `sorry`, `admit`, `stop`, or `native_decide`.
3. Lean 4 and Mathlib 4 syntax only, never Lean 3.
   Correct: `Nat.succ_le_succ`, `Nat.add_comm`, `Set.mem_setOf_eq`.
   Wrong:   `nat.succ_le_succ`, `nat.add_comm`, `set.mem_set_of_eq`.
4. Do not invent lemma names. If you are not certain a name exists, reach for a
   general tactic instead: `simp`, `simp_all`, `aesop`, `omega`, `decide`,
   `norm_num`, `linarith`, `nlinarith`, `positivity`, `ring`, `field_simp`.
5. Prefer named `have` steps over one long tactic chain, so a single wrong step
   does not invalidate the whole proof.
6. Indent with two spaces, consistently, starting at column 0 of the script.
7. Prefer tactics whose syntax you are certain of. Some traps:
   - `interval_cases x` takes the variable alone. Its `using` form needs TWO
     bound hypotheses, `interval_cases using hlo, hhi`. When in doubt use
     `rcases`, `match`, or `omega` instead.
   - `simpa ... using h` fails on associativity and commutativity mismatches.
     If the shapes differ only by rearrangement, close the step with `ring`,
     `ring_nf`, or an explicit `mul_assoc` rewrite rather than `simpa`.
   - `omega` rejects nonlinear terms. In an induction step over a polynomial,
     use `linarith` (which treats `k^2`, `k^3` as atoms) or supply the witness
     directly as `⟨w, by ring⟩`.
   A parse error means the whole block never elaborated, so nothing after the
   faulty line was checked.

Put your reasoning in `thought_process`, never in `tactics_code`.\
"""

# Sample-level strategy hints. Independent samples at a fixed prompt tend to
# converge on one approach, which wastes the parallelism; assigning each
# candidate a different route buys back the diversity.
STRATEGIES: tuple[str, ...] = (
    "",
    "Use induction on the main variable. Close the base case with `simp` or "
    "`decide`; in the step, obtain the witness from the inductive hypothesis "
    "and finish with an explicit `⟨w, by ring⟩` or with `linarith`.",
    "Avoid induction and avoid case analysis on remainders. Construct the "
    "witness directly with `refine ⟨_, ?_⟩` and close the arithmetic by `ring`.",
    "Look for an existing Mathlib lemma stating this fact or an equivalent "
    "one, and apply it with `exact`, `apply`, or `simpa using`.",
    "Use case analysis on the relevant residue or parity, via `rcases` or "
    "`Nat.even_or_odd`. Do not use `interval_cases`.",
)


# --------------------------------------------------------------------------
# structured output schemas
# --------------------------------------------------------------------------


class LeanProofResponse(BaseModel):
    thought_process: str = Field(description="Why this proof strategy should work.")
    tactics_code: str = Field(description="Tactic script only, no `by`, no fences.")


class LemmaCandidates(BaseModel):
    names: list[str] = Field(description="Mathlib 4 declaration names, fully qualified.")


# --------------------------------------------------------------------------
# result type
# --------------------------------------------------------------------------


@dataclass
class ProofResult:
    certified: bool
    proof: Optional[str]          # tactic script, without the leading `by`
    lean_result: LeanResult
    attempts: int
    source: Optional[str] = None  # the exact file Lean accepted
    diagnostics: str = ""         # Lean's output, whichever stream it used
    found_by: str = ""
    thought_process: str = ""
    history: list[tuple[str, str]] = field(default_factory=list)


# --------------------------------------------------------------------------
# text helpers
# --------------------------------------------------------------------------


def _indent(code: str, spaces: int = 2) -> str:
    """Normalise a tactic script to a fixed indentation.

    Lean 4 is whitespace sensitive after `:= by`; splicing a stripped script at
    column 0 produces parse errors that look like proof errors.
    """
    body = textwrap.dedent(code.replace("\t", "  ")).strip("\n").rstrip()
    pad = " " * spaces
    return "\n".join(pad + line if line.strip() else "" for line in body.splitlines())


def _renormalise(code: str) -> str:
    """Re-align a script whose first line lost its indentation.

    Stripping `by` or `:=` off line 1 leaves it at column 0 while the rest of
    the block keeps its original indent. `textwrap.dedent` then finds no common
    prefix and every later tactic ends up over-indented, which Lean reads as a
    continuation of the previous tactic rather than a new one.
    """
    lines = code.split("\n")
    body = [line for line in lines[1:] if line.strip()]
    if not body:
        return lines[0].strip() if lines else code

    common = min(len(line) - len(line.lstrip(" ")) for line in body)
    first = len(lines[0]) - len(lines[0].lstrip(" "))
    if lines[0].strip() and first < common:
        out = [lines[0].lstrip(" ")]
        out += [line[common:] if line.strip() else "" for line in lines[1:]]
        return "\n".join(out)
    return textwrap.dedent(code)


def _strip_preamble(code: str) -> str:
    """Remove anything the model prepended despite the schema."""
    code = code.replace("\t", "  ").strip()

    fenced = re.search(r"```(?:lean4?|)\s*\n(.*?)(?:\n```|\Z)", code, re.DOTALL)
    if fenced:
        code = fenced.group(1).strip()

    if re.match(r"^\s*(theorem|lemma|example)\b", code):
        _, sep, tail = code.partition(":=")
        if sep:
            code = tail.strip()

    while code.startswith(":="):
        code = code[2:].lstrip()
    if re.match(r"^by\b", code):
        code = code[2:]
        code = code.lstrip("\n") if "\n" in code[:2] else code.lstrip()

    return _renormalise(code.strip("\n").rstrip())


def _normalise_statement(statement: str) -> str:
    """Strip a trailing `:= by` / `:=` if the caller included one."""
    return re.sub(r":=\s*(by)?\s*$", "", statement.strip()).strip()


def _theorem_name(statement: str) -> Optional[str]:
    match = _DECL_NAME.search(statement)
    return match.group(1) if match else None


def _source(statement: str, tactics: str, trailer: str = "") -> str:
    parts = [
        "import Mathlib",
        "",
        f"set_option maxHeartbeats {MAX_HEARTBEATS} in",
        f"{statement} := by",
        _indent(tactics),
    ]
    if trailer:
        parts += ["", trailer]
    return "\n".join(parts)


def _diagnostics(result: LeanResult) -> str:
    """Collect whatever Lean said, wherever the runner put it.

    lake/lean write most diagnostics to stdout, so reading only `stderr`
    silently loses the error text on many setups and the repair loop then runs
    on an empty string.
    """
    seen: list[str] = []
    for attr in ("stderr", "stdout", "output", "messages", "message", "log"):
        value = getattr(result, attr, None)
        if isinstance(value, str) and value.strip() and value not in seen:
            seen.append(value)
    return "\n".join(seen).strip()


def _first_errors(text: str, count: int = 3, limit: int = 3000) -> str:
    """Return the first few diagnostics, not the tail.

    Lean errors cascade: the first is the real failure, the rest are noise from
    the broken proof state that followed it.
    """
    if not text:
        return "(Lean produced no diagnostic output.)"
    starts = [m.start() for m in _ERROR_HEAD.finditer(text)]
    if not starts:
        return text[:limit]
    blocks = []
    for i, start in enumerate(starts[:count]):
        end = starts[i + 1] if i + 1 < len(starts) else len(text)
        blocks.append(text[start:end].rstrip())
    return "\n".join(blocks)[:limit]


def _library_names(output: str) -> set[str]:
    """Extract missing *library* names from Lean's diagnostics.

    Lean reports `unknown identifier` for local names too: when a candidate's
    `obtain ⟨m, hm⟩ := ih` fails, the later use of `hm` raises the same error.
    Banning `hm` would tell every later prompt that a local hypothesis name is
    a nonexistent Mathlib lemma, which poisons the whole run.

    A namespaced name, or a snake_case name with several underscores, is
    library-shaped; short bare names are hypotheses. Missing a hallucinated
    root-level lemma costs one wasted retry, so the filter errs that way.
    """
    found = set()
    for name in _UNKNOWN_NAME.findall(output):
        if "." in name or name.count("_") >= 2:
            found.add(name)
    return found


def _run(source: str) -> Optional[LeanResult]:
    try:
        return check_lean(source)
    except Exception:  # a timeout or broken toolchain should not kill the run
        return None


# --------------------------------------------------------------------------
# verification
# --------------------------------------------------------------------------


def _verify(
    statement: str,
    tactics: str,
    *,
    verbose: int = 0,
) -> tuple[bool, Optional[LeanResult], str]:
    """Compile a candidate and check it is a real proof.

    Lean compiles `sorry` with only a warning, so `certified` alone is not
    enough. Reject textual escape hatches first, then ask Lean which axioms the
    finished declaration actually depends on.
    """
    if not tactics.strip():
        return False, None, "Candidate rejected: empty tactic script."

    cheat = _CHEATS.search(tactics)
    if cheat:
        return False, None, f"Candidate rejected before compiling: uses `{cheat.group(1)}`."

    name = _theorem_name(statement)
    result = _run(_source(statement, tactics))
    if result is None:
        return False, None, "Lean did not return (timeout or toolchain error)."

    output = _diagnostics(result)
    if not getattr(result, "certified", False):
        return False, result, output

    # The axioms check runs as a second compile, only once the proof itself has
    # been accepted. Appending `#print axioms` to a failing candidate makes the
    # parser report the trailer as the unexpected token, which sends the model
    # chasing a line it never wrote.
    if name:
        checked = _run(_source(statement, tactics, f"#print axioms {name}"))
        axiom_output = _diagnostics(checked) if checked else ""

        if "sorryAx" in axiom_output or "Lean.ofReduceBool" in axiom_output:
            return False, result, "Compiled, but depends on sorryAx / native_decide."

        axioms = re.search(r"depends on axioms:\s*\[([^\]]*)\]", axiom_output)
        if axioms:
            used = {a.strip() for a in axioms.group(1).split(",") if a.strip()}
            extra = used - _SAFE_AXIOMS
            if extra:
                return False, result, f"Depends on unexpected axioms: {sorted(extra)}"
            if verbose >= 2:
                print(f"Axiom check passed: {sorted(used) or 'no axioms'}")

    return True, result, output


# --------------------------------------------------------------------------
# stage 1 — cheap tactics, no API call
# --------------------------------------------------------------------------


def _ladder_body(tactics) -> str:
    """Build a `first | ... | ...` block that backtracks on partial progress.

    `first` commits to the first branch that does not throw, and a tactic like
    `simp` can succeed while leaving goals open. Without the trailing `done`
    the block would stop at that branch and the compile would fail with
    `unsolved goals`, never reaching a later tactic that would have finished.
    """
    return "first\n" + "\n".join(f"| ({t}; done)" for t in tactics)


def _try_tactics(statement: str, verbose: int) -> tuple[Optional[str], Optional[LeanResult]]:
    """One compile to see whether any standard tactic closes the goal, then a
    bisection (about four more compiles) to find which one."""
    if verbose >= 1:
        print(f"[tactics] Trying {len(LADDER)} standard tactics in one compile...")

    ok, result, _ = _verify(statement, _ladder_body(LADDER), verbose=verbose)
    if not ok:
        if verbose >= 1:
            print("[tactics] None closed the goal.")
        return None, result

    lo, hi = 0, len(LADDER)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        hit, _, _ = _verify(statement, _ladder_body(LADDER[lo:mid]), verbose=0)
        if hit:
            hi = mid
        else:
            lo = mid

    winner = LADDER[lo]
    ok, result, _ = _verify(statement, winner, verbose=verbose)
    if not ok:  # shouldn't happen; fall back to the whole ladder
        winner = _ladder_body(LADDER)
        ok, result, _ = _verify(statement, winner, verbose=verbose)
    if verbose >= 1:
        print(f"[tactics] Closed by `{winner}`.")
    return (winner if ok else None), result


# --------------------------------------------------------------------------
# model calls (structured outputs)
# --------------------------------------------------------------------------


def _parse_endpoint(client: OpenAI):
    """`parse` moved out of `beta` in recent SDKs; support both."""
    chat = getattr(client, "chat", None)
    if chat is not None and hasattr(chat.completions, "parse"):
        return chat.completions.parse
    return client.beta.chat.completions.parse


def _ask(
    client: OpenAI,
    model: str,
    system: str,
    user: str,
    schema: type[BaseModel],
    effort: Optional[str],
):
    """One structured-output call, with graceful fallback if the model does not
    accept `reasoning_effort`."""
    endpoint = _parse_endpoint(client)
    kwargs = {
        "model": model,
        "messages": [
            {"role": "system", "content": system},
            {"role": "user", "content": user},
        ],
        "response_format": schema,
    }
    if effort:
        try:
            response = endpoint(**kwargs, reasoning_effort=effort)
        except Exception:
            response = endpoint(**kwargs)
    else:
        response = endpoint(**kwargs)

    message = response.choices[0].message
    if getattr(message, "refusal", None):
        raise RuntimeError(f"Model refused: {message.refusal}")
    if message.parsed is None:
        raise RuntimeError("Model returned no parseable structured output.")
    return message.parsed


# --------------------------------------------------------------------------
# stage 2 — ground the lemma names against the real Mathlib
# --------------------------------------------------------------------------


def _ground_lemmas(
    client: OpenAI,
    model: str,
    statement: str,
    effort: Optional[str],
    verbose: int,
) -> tuple[list[str], list[str]]:
    """Ask the model which Mathlib lemmas it wants, then ask Lean which of them
    exist. A name that does not exist yields the same `unknown identifier`
    error on every retry, so catching these up front is cheaper than letting
    the repair loop rediscover them one at a time."""
    user = (
        "List up to 12 Mathlib (Lean 4) declaration names likely useful for "
        "proving this theorem. Fully qualified names only.\n\n" + statement
    )
    try:
        proposed = _ask(client, model, SYSTEM_PROMPT, user, LemmaCandidates, effort).names
    except Exception as exc:
        if verbose >= 1:
            print(f"[grounding] Skipped ({exc}).")
        return [], []

    names = [n.strip().strip("`") for n in proposed]
    names = [n for n in dict.fromkeys(names) if _LEAN_IDENT.match(n)][:12]
    if not names:
        return [], []

    checks = "\n".join(f"#check @{n}" for n in names)
    result = _run(f"import Mathlib\n\n{checks}")
    if result is None:
        return names, []

    output = _diagnostics(result)
    # Only names we proposed can be missing here, so intersect rather than
    # filtering by shape; root-level lemmas like `mul_comm` have no namespace.
    missing = set(_UNKNOWN_NAME.findall(output)) & set(names)
    for name in names:  # any name named in an error line is suspect
        if re.search(rf"error:[^\n]*{re.escape(name)}", output, re.IGNORECASE):
            missing.add(name)

    real = [n for n in names if n not in missing]
    if verbose >= 1:
        print(f"[grounding] {len(real)} of {len(names)} proposed names exist.")
    if verbose >= 2 and missing:
        print(f"[grounding] Nonexistent: {sorted(missing)}")
    return real, sorted(missing)


# --------------------------------------------------------------------------
# stage 3 — sampled generation with a history-carrying repair loop
# --------------------------------------------------------------------------


def _build_user_prompt(
    statement: str,
    history: list[tuple[str, str]],
    known: list[str],
    banned: set[str],
) -> str:
    sections = [f"Theorem to prove:\n```lean\n{statement} := by\n```"]

    if known:
        sections.append(
            "These declarations were verified to exist in this Mathlib build; "
            "prefer them:\n" + "\n".join(f"- {n}" for n in known)
        )
    if banned:
        sections.append(
            "These names do NOT exist in this Mathlib build. Never use them:\n"
            + "\n".join(f"- {n}" for n in sorted(banned))
        )
    if history:
        blocks = []
        for i, (tactics, errors) in enumerate(history[-3:], 1):
            blocks.append(
                f"--- Rejected attempt {i} ---\n```lean\nby\n{_indent(tactics)}\n```\n"
                f"Lean diagnostic:\n{errors}"
            )
        sections.append(
            "Previous attempts failed. Identify the step that broke "
            "type-checking and take a different approach; do not resubmit a "
            "variant of the same script.\n\n" + "\n\n".join(blocks)
        )

    return "\n\n".join(sections)


def _sample(
    client: OpenAI,
    model: str,
    user: str,
    n: int,
    effort: Optional[str],
    max_workers: int,
    diversify: bool = True,
) -> list[tuple[str, str]]:
    """Return (tactics, thought_process) pairs.

    Each sample approaches the goal independently, so the set explores
    different proof strategies rather than variations on one. Generation is
    network-bound, so the calls overlap; compilation downstream is serial.
    """

    def one(index: int) -> tuple[str, str]:
        prompt = user
        if diversify and n > 1:
            hint = STRATEGIES[index % len(STRATEGIES)]
            if hint:
                prompt = f"{user}\n\nFor this candidate specifically: {hint}"
        parsed = _ask(client, model, SYSTEM_PROMPT, prompt, LeanProofResponse, effort)
        return _strip_preamble(parsed.tactics_code), parsed.thought_process

    if n == 1:
        return [one(0)]

    results: list[tuple[str, str]] = []
    workers = max(1, min(n, max_workers))
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(one, i) for i in range(n)]
        for future in concurrent.futures.as_completed(futures):
            try:
                results.append(future.result())
            except Exception:
                continue
    return results


# --------------------------------------------------------------------------
# public entry point
# --------------------------------------------------------------------------


def prove(
    theorem_statement: str,
    *,
    model: str = "gpt-5",
    max_attempts: int = 3,
    verbose: int = 0,
    samples_per_attempt: int = 4,
    reasoning_effort: Optional[str] = "high",
    try_tactics: bool = True,
    ground_lemmas: bool = True,
    diversify: bool = True,
    max_workers: int = 4,
) -> ProofResult:
    """
    Generate and Lean-certify a proof.

    `theorem_statement` must include `theorem ... : ...`; a trailing `:= by` is
    stripped if present. `ProofResult.proof` is the tactic script without the
    leading `by`; `ProofResult.source` is the exact file Lean accepted.

    verbose=1 prints progress, verbose=2 also prints candidates and diagnostics.

    Options:
      samples_per_attempt  independent candidates per round. Sampling explores
                           different proof strategies; repair refines one. Both
                           are useful and the right balance depends on the
                           theorems, so benchmark before settling on a value.
      reasoning_effort     passed through when the model accepts it.
      try_tactics          run the standard tactic ladder before any API call.
      ground_lemmas        verify proposed lemma names against Mathlib first.
      diversify            give each candidate in a round a different strategy
                           hint, so the samples explore rather than converge.
    """
    if max_attempts < 1:
        raise ValueError("max_attempts must be at least 1.")
    if samples_per_attempt < 1:
        raise ValueError("samples_per_attempt must be at least 1.")

    statement = _normalise_statement(theorem_statement)

    last_result: Optional[LeanResult] = None
    history: list[tuple[str, str]] = []
    banned: set[str] = set()
    tried: set[str] = set()
    attempts_used = 0

    # --- stage 1 -----------------------------------------------------------
    if try_tactics:
        tactics, last_result = _try_tactics(statement, verbose)
        if tactics is not None:
            return ProofResult(
                certified=True,
                proof=tactics,
                lean_result=last_result,
                attempts=0,
                source=_source(statement, tactics),
                diagnostics=_diagnostics(last_result) if last_result else "",
                found_by="tactic-ladder",
                thought_process="Closed by a standard Mathlib tactic.",
                history=history,
            )

    load_dotenv()
    if not os.environ.get("OPENAI_API_KEY"):
        raise RuntimeError("OPENAI_API_KEY is missing. Add it to .env.")
    client = OpenAI()

    # --- stage 2 -----------------------------------------------------------
    known: list[str] = []
    if ground_lemmas:
        known, missing = _ground_lemmas(client, model, statement, reasoning_effort, verbose)
        banned.update(missing)

    # --- stage 3 -----------------------------------------------------------
    for attempt in range(1, max_attempts + 1):
        attempts_used = attempt
        if verbose >= 1:
            print(
                f"[attempt {attempt}/{max_attempts}] Requesting "
                f"{samples_per_attempt} candidate(s) from {model}..."
            )

        user_prompt = _build_user_prompt(statement, history, known, banned)
        candidates = _sample(
            client, model, user_prompt, samples_per_attempt,
            reasoning_effort, max_workers, diversify,
        )

        fresh: list[tuple[str, str]] = []
        for tactics, thought in candidates:
            key = re.sub(r"\s+", " ", tactics)
            if tactics and key not in tried:
                tried.add(key)
                fresh.append((tactics, thought))

        if not fresh:
            if verbose >= 1:
                print(f"[attempt {attempt}/{max_attempts}] No new candidates.")
            continue

        for index, (tactics, thought) in enumerate(fresh, 1):
            if verbose >= 1:
                print(
                    f"[attempt {attempt}/{max_attempts}] Checking candidate "
                    f"{index}/{len(fresh)} with Lean..."
                )
            if verbose >= 2:
                print("Candidate proof:\nby")
                print(_indent(tactics))

            ok, result, output = _verify(statement, tactics, verbose=verbose)
            if result is not None:
                last_result = result

            if ok:
                if verbose >= 1:
                    print(f"[attempt {attempt}/{max_attempts}] Lean certified the proof.")
                return ProofResult(
                    certified=True,
                    proof=tactics,
                    lean_result=last_result,
                    attempts=attempt,
                    source=_source(statement, tactics),
                    diagnostics=output,
                    found_by=f"{model} (attempt {attempt}, candidate {index})",
                    thought_process=thought,
                    history=history,
                )

            errors = _first_errors(output)
            banned.update(_library_names(output))
            history.append((tactics, errors))
            if verbose >= 1:
                print(f"[attempt {attempt}/{max_attempts}] Lean rejected candidate {index}.")
            if verbose >= 2:
                print("Lean diagnostic:")
                print(errors)

    if verbose >= 1:
        print(f"No certified proof after {attempts_used} attempt(s).")

    if last_result is None:  # nothing ever reached the compiler
        last_result = _run(_source(statement, "skip"))

    return ProofResult(
        certified=False,
        proof=None,
        lean_result=last_result,
        attempts=attempts_used,
        source=None,
        diagnostics=_diagnostics(last_result) if last_result else "",
        found_by="",
        thought_process="",
        history=history,
    )