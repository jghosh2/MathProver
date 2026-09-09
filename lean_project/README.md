# Lean certification backend

This directory is the Lean 4 and Mathlib project used by the parent
[`MathProver`](../README.md) Python package. Its job is deliberately narrow:
it provides the reproducible Lean environment that checks whether a proposed
proof is valid.

```text
Python / notebook
  -> writes a temporary `.lean` file in this directory
  -> runs `lake env lean <temporary-file>.lean`
  -> reads Lean's success status and diagnostics
```

Lean, not the Python code or the language model, is the authority on
certification. A theorem is accepted only when `lake env lean` exits with
status `0`.

## Contents

- `lakefile.toml` declares this Lake project and pins Mathlib.
- `lake-manifest.json` records resolved package versions for reproducible
  builds.
- `lean-toolchain` pins the Lean toolchain version used by the project.
- `Main.lean` is a small manual smoke test.
- `LeanProject/` contains the generated Lean library scaffold; it can hold
  hand-written supporting lemmas in the future.

The parent library currently imports `Mathlib` in each generated source file,
so its temporary proofs can use Mathlib theorems and tactics such as `simp`,
`ring`, and `omega` where appropriate.

## One-time setup

From this directory, after installing Lean through `elan`:

```bash
lake exe cache get
lake build
```

`lake exe cache get` downloads Mathlib's compiled cache and can take time and
several GB of disk space. It is generally needed only during first setup or
after changing dependencies.

Check that Lean and Lake are available first:

```bash
lean --version
lake --version
```

## Verify the local installation

`Main.lean` contains a small theorem:

```lean
import Mathlib

theorem add_zero_test (n : Nat) : n + 0 = n := by
  simp
```

Check it with:

```bash
lake env lean Main.lean
```

On success, Lean normally prints no output and returns to your shell prompt.
Any output on standard error is a diagnostic explaining why the source did not
compile.

You can also build the whole Lean project:

```bash
lake build
```

## How MathProver uses this directory

`src/mathprover/lean_runner.py` creates a temporary `.lean` file here rather
than in an arbitrary temporary directory. That ensures `lake env lean` can see
this project's Mathlib dependency and uses the Lean version pinned by
`lean-toolchain`.

For example, this complete source is suitable for checking:

```lean
import Mathlib

theorem add_comm_test (a b : Nat) : a + b = b + a := by
  simpa using Nat.add_comm a b
```

The generated temporary file is deleted after each check. No model-generated
proofs are retained here by default.

## Developing Lean code here

Open the parent `MathProver` folder in Cursor or VS Code and install the
official Lean 4 extension. It provides interactive diagnostics and goal views
for files in this project.

When adding hand-written Lean modules:

1. Place them under `LeanProject/`.
2. Import them from `LeanProject.lean` or from the file that needs them.
3. Run `lake build` before relying on them from Python.

Keep this directory as part of the parent Git repository. Do not run `git init`
inside `lean_project`; a nested Git repository prevents the parent project from
tracking these files normally.

## Troubleshooting

### `lake: command not found`

Restart Terminal after installing `elan`, or make its tools available in the
current session:

```bash
source "$HOME/.elan/env"
```

### First build is slow

Run `lake exe cache get`, then `lake build`. Initial Mathlib download and cache
installation are substantially slower than ordinary proof checks.

### A proof from Python fails

Read the Lean diagnostic returned by `certify()` or `prove()`. It identifies
the exact failure in the generated Lean source. A model-generated proof is not
valid unless the result reports `certified=True`.
