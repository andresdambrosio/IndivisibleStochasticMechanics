/-
Copyright (c) 2026 NewQuantumMechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib

/-!
# Stochastic matrices and probability distributions on a configuration space

In Barandes' stochastic-quantum correspondence a physical system is described by a
*finite configuration space* `C` (here, any `Fintype n`) together with transition
probabilities

  `Γ i j (t) = P(i at time t | j at time 0)`.

We use the **column-stochastic** convention of Barandes: the entries are nonnegative and
each column sums to one. This is Mathlib's `Matrix.colStochastic ℝ n`, a submonoid of
`Matrix n n ℝ` (so it contains `1` and is closed under products). A probability
distribution `p` evolves as `p(t) = Γ(t) *ᵥ p(0)`.

## References

* J. A. Barandes, *The Stochastic-Quantum Correspondence*, arXiv:2302.10778.
* J. A. Barandes, *The Stochastic-Quantum Theorem*, arXiv:2309.03085.
-/

@[expose] public section

open Matrix

namespace NQM

variable {n : Type*} [Fintype n]

/-- A probability distribution on the configuration space `n`. -/
structure IsProbDist (p : n → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ p i
  sum_eq_one : ∑ i, p i = 1

/-- Column-stochastic matrices map probability distributions to probability distributions. -/
theorem IsProbDist.mulVec [DecidableEq n] {Γ : Matrix n n ℝ} (hΓ : Γ ∈ colStochastic ℝ n)
    {p : n → ℝ} (hp : IsProbDist p) : IsProbDist (Γ *ᵥ p) where
  nonneg := nonneg_mulVec_of_mem_colStochastic hΓ hp.nonneg
  sum_eq_one := by rw [sum_mulVec_of_mem_colStochastic hΓ, hp.sum_eq_one]

end NQM
