/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Stochastic.Basic

/-!
# Unistochastic matrices and the Born-rule representation

The bridge between indivisible stochastic processes and Hilbert-space quantum theory is
the observation that a stochastic matrix can be written entrywise as a squared modulus

  `Γ i j = ‖Θ i j‖²`,

for some complex matrix `Θ` (a *Born representation*). When `Θ` can be chosen unitary,
`Γ` is called *unistochastic*. Unitary time evolution `U(t)` of a quantum system therefore
induces the stochastic transition matrices `Γ(t) i j = ‖U(t) i j‖²` of Barandes'
correspondence.

## Main definitions

* `ISM.IsBornRep Γ Θ`: `Θ` is a Born representation of `Γ`.
* `ISM.IsUnistochastic Γ`: `Γ` has a unitary Born representation.

## Main results

* `ISM.IsUnistochastic.mem_colStochastic`: every unistochastic matrix is stochastic.

## References

* J. A. Barandes, *The Stochastic-Quantum Theorem*, arXiv:2309.03085.
-/

@[expose] public section

open Matrix

namespace ISM

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Θ` is a Born representation of `Γ`: `Γ i j = ‖Θ i j‖²` for all `i, j`. -/
def IsBornRep (Γ : Matrix n n ℝ) (Θ : Matrix n n ℂ) : Prop :=
  ∀ i j, Γ i j = ‖Θ i j‖ ^ 2

/-- `Γ` is *unistochastic* if it admits a unitary Born representation. -/
def IsUnistochastic (Γ : Matrix n n ℝ) : Prop :=
  ∃ U ∈ Matrix.unitaryGroup n ℂ, IsBornRep Γ U

/-- The columns of a unitary matrix are unit vectors: `∑ i, ‖U i j‖² = 1`. -/
theorem unitary_col_normSq_sum {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (j : n) : ∑ i, ‖U i j‖ ^ 2 = 1 := by
  -- `(Uᴴ * U) j j = ∑ i, conj (U i j) * U i j = 1`.
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU) j) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.star_def,
    Complex.conj_mul'] at h
  exact_mod_cast h

/-- Every unistochastic matrix is stochastic. -/
theorem IsUnistochastic.mem_colStochastic {Γ : Matrix n n ℝ} (h : IsUnistochastic Γ) :
    Γ ∈ colStochastic ℝ n := by
  obtain ⟨U, hU, hΓ⟩ := h
  refine mem_colStochastic_iff_sum.mpr ⟨fun i j => ?_, fun j => ?_⟩
  · rw [hΓ i j]; positivity
  · rw [Finset.sum_congr rfl fun i _ => hΓ i j]; exact unitary_col_normSq_sum hU j

end ISM
