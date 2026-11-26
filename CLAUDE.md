# CLAUDE.md

Guidance for Claude Code (and other AI agents) working in this repository.

## What this project is

A Lean 4 + Mathlib formalization of Jacob Barandes' reformulation of quantum mechanics as
**indivisible stochastic processes** ("Indivisible Stochastic Mechanics", ISM), plus a
bilingual course book (English default, Spanish) by Andrés D'Ambrosio that explains every
step. The long-term goal is to show, in machine-checked
form, that ISM is equivalent to all of quantum mechanics. Read `ROADMAP.md` first.

## Where things are

| Path | Contents |
|---|---|
| `IndivisibleStochasticMechanics/Stochastic/` | stochastic matrices, generalized processes, division events, Born representations |
| `IndivisibleStochasticMechanics/Quantum/` | unitary processes, dilations (the correspondence), density matrices, channels, measurement, collapse, decoherence |
| `IndivisibleStochasticMechanics/Examples/` | the indivisible qubit, measured, and partially decohered |
| `IndivisibleStochasticMechanics/ForMathlib/` | general results to upstream to Mathlib (Mathlib namespaces, no project imports) |
| `TRUSTED.md` | the trusted layer: every definition and main statement, with source and review status |
| `ROADMAP.md` | the full plan, with what is done |
| `book/en/`, `book/es/` | the course book in English (default, site root) and Spanish (voseo, under `es/`), same file names; mdBook + KaTeX, published to GitHub Pages |
| `book/theme/` | shared mdBook theme overrides: the "Warm" theme and the EN/ES switch (pinned to mdBook 0.5.4) |
| `scripts/check_trusted.py` | CI check that every definition is listed in `TRUSTED.md` |

## Workflow for every change

1. `export PATH="$HOME/.elan/bin:$PATH"`, which is needed in non-login shells.
2. Prototype hard proofs in a scratch file with `lake env lean <file>` before editing the library.
3. `lake build --wfail` must pass: no warnings, no `sorry`.
4. Any new `def`/`structure` goes into `TRUSTED.md` as ⏳, with source and interpretive notes.
   Add main theorems whose *statements* carry physics. **Never mark an entry ✅**: only a
   human reviewer does that.
5. `python3 scripts/check_trusted.py` must pass.
6. Update `ROADMAP.md`, `README.md` (module table), and the book **in both languages**:
   write a new chapter or update the existing one in `book/en/` and `book/es/`, then update
   `SUMMARY.md`, `README.md` and `99-references.md` in each. **Attribution:** credit every
   idea to its author with a citation and link in the paragraph where it appears; say
   explicitly what is original to the project, and never present others' work as ours.
7. Commit with a descriptive message, push, and check CI (`gh run list`). Both workflows
   must pass: "Lean build" (build + trusted-layer) and "Book". Then check that the book
   page has no `katex-error`.

## Conventions

- Namespace `ISM`. Files start with `module`, use `public import`, and `@[expose] public section`.
- Mathlib style; lines at most 100 characters. Cite the paper in docstrings.
- Column-stochastic convention: `Γ i j = P(i at t | j at 0)`, using Mathlib's `Matrix.colStochastic`.
- Useful idioms already in the code: `open ComplexOrder` for `PosSemidef` over ℂ; `open Kronecker` for `⊗ₖ`;
  environments and pointers are `Option n` with `none` = ready/initial; completing orthonormal
  columns to a unitary is `Matrix.exists_mem_unitaryGroup_of_orthonormal`; and the norm of a column
  is `sum_norm_sq_col_eq_conjTranspose_mul_self` / `unitary_col_normSq_sum`.
- `simp` turns `↑(Real.cos t)` into `Complex.cos ↑t`. Use `-Complex.ofReal_cos` when that gets in the way.

## Contribution model

AI-first: proofs are free, because Lean checks them. Definitions, main statements and
references need human review in `TRUSTED.md`. When upstreaming to Mathlib or physlib,
their stricter AI policies apply. See `CONTRIBUTING.md`.
