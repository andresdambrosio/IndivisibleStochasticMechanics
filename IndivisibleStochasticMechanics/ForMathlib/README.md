# ForMathlib

Results that are **not specific to this project** and belong in
[Mathlib](https://github.com/leanprover-community/mathlib4). We build them here so that we
are never blocked by Mathlib's review pace, and we upstream them in small pull requests.
The FLT project and others follow the same pattern.

## Rules

- Files mirror Mathlib's directory layout: `ForMathlib/Matrix/Unitary.lean` is meant to
  become part of `Mathlib/LinearAlgebra/Matrix/...` or similar.
- Declarations go in Mathlib's namespaces (e.g. `Matrix`), not in `ISM`.
- Code follows Mathlib style and naming strictly, so that upstreaming is a copy, not a rewrite.
- Nothing in `ForMathlib/` may import anything from the rest of this project.
- **Upstreaming follows Mathlib's own rules**, including its policy on AI-assisted
  contributions. A human opens the PR, answers reviewers personally, and must be able to
  vouch for every line. That is stricter than our internal model (see CONTRIBUTING.md).
- After a result lands in Mathlib, delete it here and bump the Mathlib dependency.

## Status

| Declaration | File | Upstream status |
|---|---|---|
| `Matrix.exists_mem_unitaryGroup_of_orthonormal` | `Matrix/Unitary.lean` | not yet proposed |
| `Matrix.sum_norm_sq_col_eq_conjTranspose_mul_self` | `Matrix/Unitary.lean` | not yet proposed; check whether Mathlib already has it in another form |

## What Mathlib is missing for infinite-dimensional quantum mechanics

These are the large pieces of infrastructure needed for Stage II of the roadmap. Each one
is a substantial project on its own. Before starting any of them, ask on the Lean Zulip
whether someone is already working on it.

| Piece | Why we need it | In Mathlib today |
|---|---|---|
| Spectral measures and the spectral theorem for unbounded self-adjoint operators | observables like position, momentum, energy | compact and finite-dimensional cases only |
| Stone's theorem | `U(t) = exp(-itH)` for unbounded `H` | missing |
| Strongly continuous (C₀) semigroups | time evolution in infinite dimensions | missing |
| Density operators and quantum channels on Hilbert spaces | open systems, measurement | partial (trace class) |
| Markov kernels on continuous configuration spaces | the stochastic side | present (`ProbabilityTheory.Kernel`) |
