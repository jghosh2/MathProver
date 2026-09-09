# MathProver

MathProver is a small Python-based prototype for generating and formally
certifying Lean 4 proofs.

The language model proposes a Lean proof. Lean is the verifier and the sole
authority on whether a claim is proved: a result is `certified=True` only when
Lean accepts the complete generated source file.

```text
Lean theorem statement
        |
        v
OpenAI proposes a `by ...` proof
        |
        v
Python invokes Lean + Mathlib
        |
        +-- accepted --> certified proof
        |
        +-- rejected --> Lean diagnostic -> retry (up to a limit)
```

## What this prototype does

- `certify()` checks a complete Lean source string locally.
- `prove()` takes a Lean theorem statement, asks OpenAI for a proof, and uses
  Lean to check it.
- If Lean rejects a candidate, `prove()` gives the diagnostic to the model and
  retries up to three times by default.

It does **not** currently formalize natural-language claims. The input to
`prove()` must be a Lean theorem statement. This is deliberate: Lean proves
the precise formal statement it receives, not an informal interpretation.

## Repository layout

```text
MathProver/
├── .env                    # local API key; never commit this
├── .gitignore
├── pyproject.toml
├── lean_project/           # Lean 4 + Mathlib project
│   └── Main.lean
├── notebooks/
│   └── 01_first_proof.ipynb
└── src/mathprover/
    ├── __init__.py
    ├── api.py              # public Python API
    ├── lean_runner.py      # invokes Lean and collects diagnostics
    └── proof_search.py     # OpenAI generation and repair loop
```

## Prerequisites

You need:

1. Python 3.11 or later. Miniconda is optional but works well for managing the
   Python environment and Jupyter kernel.
2. Lean 4 and its `lake` build tool, installed through `elan`.
3. An OpenAI API key.
4. Git, if you want version control.

Cursor can be used instead of VS Code. Install the official **Lean 4**
extension in Cursor for interactive Lean diagnostics and goal views.

## Set up from scratch

### 1. Install Lean and create the Mathlib project

On macOS, first verify that Git is available (macOS will offer to install the
Xcode Command Line Tools if it is not):

```bash
git --version
```

Install `elan`, Lean's toolchain manager:

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

When prompted, choose option `1` to accept the default installation. Close and
reopen Terminal afterwards. Alternatively, make the tools available in the
current Terminal session immediately:

```bash
source "$HOME/.elan/env"
```

Check that Lean and Lake are available:

```bash
lean --version
lake --version
```

If you are creating this project from scratch, run the following from the
directory that will contain `MathProver`:

```bash
mkdir MathProver
cd MathProver
lake +leanprover-community/mathlib4:lean-toolchain new lean_project math
cd lean_project
lake exe cache get
lake build
cd ..
```

`lake exe cache get` downloads Mathlib's precompiled cache and can be several
GB. It is normally only needed when setting up or changing dependencies.

Verify Lean with `lean_project/Main.lean`:

```lean
import Mathlib

theorem add_zero_test (n : Nat) : n + 0 = n := by
  simp
```

Then run:

```bash
cd lean_project
lake env lean Main.lean
cd ..
```

No output and a returned shell prompt means the theorem compiled successfully.

### 2. Create the Python environment

Using Conda:

```bash
conda create -n mathprover python=3.12
conda activate mathprover
```

Or, using Python's built-in virtual environment:

```bash
python3 -m venv .venv
source .venv/bin/activate
```

Install the project and notebook tools from the top-level `MathProver` folder:

```bash
python -m pip install --upgrade pip
python -m pip install -e .
python -m pip install jupyterlab ipykernel pytest
```

For Conda, expose this environment as a notebook kernel:

```bash
python -m ipykernel install --user --name mathprover --display-name "Python (mathprover)"
```

### 3. Configure the API key

Create a top-level `.env` file. Do not put this value in a notebook or source
file:

```text
OPENAI_API_KEY=your_api_key_here
```

Make sure `.gitignore` contains:

```text
.env
.venv/
__pycache__/
.ipynb_checkpoints/
```

If Git has not been initialized, do so at the repository root:

```bash
git init
git check-ignore -v .env
```

The second command should show that `.env` is ignored.

## Run the workflow

Start JupyterLab from the top-level project folder:

```bash
jupyter lab
```

Open `notebooks/01_first_proof.ipynb`, choose the `Python (mathprover)` kernel
(or the environment used above), and use either workflow below.

### A. Certify a proof you supply

`certify()` requires complete Lean code, including the import:

```python
from mathprover import certify

source = """
import Mathlib

theorem add_zero_test (n : Nat) : n + 0 = n := by
  simp
"""

result = certify(source)
print("Certified:", result.certified)
print(result.stderr)
```

Expected result:

```text
Certified: True
```

Lean should reject an invalid theorem:

```python
bad_source = """
import Mathlib

theorem false_claim : 1 = 2 := by
  rfl
"""

result = certify(bad_source)
print("Certified:", result.certified)
print(result.stderr)
```

Expected result: `Certified: False`, followed by Lean's diagnostic.

### B. Generate and certify a proof

`prove()` adds `import Mathlib` itself. Supply a Lean theorem declaration but
omit `:= by` and the proof body:

```python
from mathprover import prove

result = prove("""
theorem add_comm_test (a b : Nat) : a + b = b + a
""")

print("Certified:", result.certified)
print("Attempts:", result.attempts)
print("Proof:")
print(result.proof)
print(result.lean_result.stderr)
```

On success, `result.proof` contains Lean code such as:

```lean
by
  simpa using Nat.add_comm a b
```

The default model is `gpt-5`, and the default maximum is three attempts. For a
quicker experiment, restrict it to a single attempt:

```python
result = prove(
    """theorem add_comm_test (a b : Nat) : a + b = b + a""",
    max_attempts=1,
)
```

## Important conventions

| Function | Required input | Who supplies `import Mathlib`? |
| --- | --- | --- |
| `certify(source)` | Complete Lean source, proof included | You |
| `prove(theorem_statement)` | `theorem ... : ...`, without `:= by` | MathProver |

Never treat a model response alone as proof. Only use `result.certified` to
determine whether a theorem has been formally verified.

## Troubleshooting

### `ModuleNotFoundError: No module named 'mathprover'`

The notebook is using a different Python environment. In a notebook cell, run:

```python
import sys
!{sys.executable} -m pip install -e ..
```

Restart the kernel afterwards. Then choose the `Python (mathprover)` kernel.

### `lake: command not found`

Lean's `elan` installation is not on your terminal path. Close and reopen
Terminal after installing `elan`, then run `lake --version` again.

### Lean command seems to do nothing

If the prompt returned, a successful Lean command generally produces no output.
The first Mathlib setup can take longer; run `lake exe cache get` and then
`lake build` from `lean_project`.

### A generated proof takes a long time

Lean checks are usually fast. Most of the time is spent waiting for one or
more model calls. `prove()` may make up to `max_attempts` calls; use
`max_attempts=1` while experimenting. A difficult theorem may require better
prompts, more attempts, or retrieval of relevant Mathlib lemmas.

## Next directions

1. Add a test suite of 20–50 Lean theorem statements and track certification
   rate, number of attempts, and latency.
2. Add a user-reviewed natural-language-to-Lean formalization step.
3. Add retrieval over trusted Mathlib documentation and previously certified
   proofs before introducing a knowledge graph or multi-agent orchestration.
4. Add structured logging and a configurable API timeout before running large
   batches.

## References

- [Lean installation guide](https://lean-lang.org/install/)
- [Lean Lake build tool documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
- [OpenAI API quickstart](https://platform.openai.com/docs/quickstart/make-your-first-api-request)
