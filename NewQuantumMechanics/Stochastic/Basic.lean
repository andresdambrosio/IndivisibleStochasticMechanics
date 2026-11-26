/-
Copyright (c) 2026 NewQuantumMechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Stochastic matrices and probability distributions on a configuration space

In Barandes' stochastic-quantum correspondence a physical system is described by a
*finite configuration space* `C` (here, any `Fintype n`) together with transition
probabilities

  `Γ i j (t) = P(i at time t | j at time 0)`.

We use the **column-stochastic** convention of Barandes: the entries are nonnegative and
each column sums to one. A probability distribution `p` evolves as `p(t) = Γ(t) *ᵥ p(0)`.

## References

* J. A. Barandes, *The Stochastic-Quantum Correspondence*, arXiv:2302.10778.
* J. A. Barandes, *The Stochastic-Quantum Theorem*, arXiv:2309.03085.
-/

open Matrix

namespace NQM

variable {n : Type*} [Fintype n]

/-- A probability distribution on the configuration space `n`. -/
structure IsProbDist (p : n → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ p i
  sum_eq_one : ∑ i, p i = 1

/-- A column-stochastic matrix: `Γ i j` is the probability of ending in configuration `i`
given that the system started in configuration `j`. -/
structure IsStochastic (Γ : Matrix n n ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ Γ i j
  col_sum : ∀ j, ∑ i, Γ i j = 1

namespace IsStochastic

/-- The identity matrix is stochastic (no evolution). -/
theorem one [DecidableEq n] : IsStochastic (1 : Matrix n n ℝ) where
  nonneg i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  col_sum j := by
    simp [Matrix.one_apply]

/-- Stochastic matrices map probability distributions to probability distributions. -/
theorem mulVec_isProbDist {Γ : Matrix n n ℝ} (hΓ : IsStochastic Γ) {p : n → ℝ}
    (hp : IsProbDist p) : IsProbDist (Γ *ᵥ p) where
  nonneg i := Finset.sum_nonneg fun j _ => mul_nonneg (hΓ.nonneg i j) (hp.nonneg j)
  sum_eq_one := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    simp [← Finset.sum_mul, hΓ.col_sum, hp.sum_eq_one]

/-- The product of two stochastic matrices is stochastic (composition of processes). -/
theorem mul {Γ Δ : Matrix n n ℝ} (hΓ : IsStochastic Γ) (hΔ : IsStochastic Δ) :
    IsStochastic (Γ * Δ) where
  nonneg i j := Finset.sum_nonneg fun k _ => mul_nonneg (hΓ.nonneg i k) (hΔ.nonneg k j)
  col_sum j := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp [← Finset.sum_mul, hΓ.col_sum, hΔ.col_sum]

end IsStochastic

end NQM
