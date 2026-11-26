/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Quantum.DensityMatrix

/-!
# Quantum channels and stochastic matrices

A quantum channel in Kraus form is a family of matrices `K k` with `∑ k, (K k)ᴴ * K k = 1`,
acting on density matrices as `ρ ↦ ∑ k, K k * ρ * (K k)ᴴ`. Channels describe open systems,
noise, and measurement. Unitary evolution is the special case of a single Kraus operator.

Read in the configuration basis, every channel induces the transition matrix

  `Γ i j = ∑ k, ‖K k i j‖²`,

which is stochastic. Conversely, **every stochastic matrix arises this way**, from the
"classical" Kraus operators `K (a, b) = √Γ_ab · |a⟩⟨b|`. Quantum channels and stochastic
matrices therefore describe the same single-time transition statistics.

## Main results

* `ISM.IsKrausFamily.krausTransition_mem_colStochastic`: channels induce stochastic matrices.
* `ISM.krausChannel_diagonal_apply_self`: on a mixture of configurations `diag(p)`, the
  channel's output diagonal is `Γ p`.
* `ISM.classicalKraus_isKrausFamily`, `ISM.krausTransition_classicalKraus`: every
  stochastic matrix is the transition matrix of a quantum channel.
-/

@[expose] public section

open Matrix

namespace ISM

variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]

/-- A family of Kraus operators: `∑ k, (K k)ᴴ * K k = 1`. -/
def IsKrausFamily (K : κ → Matrix n n ℂ) : Prop :=
  ∑ k, (K k)ᴴ * K k = 1

/-- The quantum channel `ρ ↦ ∑ k, K k * ρ * (K k)ᴴ`. -/
noncomputable def krausChannel (K : κ → Matrix n n ℂ) (ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ k, K k * ρ * (K k)ᴴ

/-- Transition probabilities of a channel in the configuration basis:
`Γ i j = ∑ k, ‖K k i j‖²`. -/
noncomputable def krausTransition (K : κ → Matrix n n ℂ) : Matrix n n ℝ :=
  Matrix.of fun i j => ∑ k, ‖K k i j‖ ^ 2

/-- Quantum channels induce stochastic matrices. -/
theorem IsKrausFamily.krausTransition_mem_colStochastic {K : κ → Matrix n n ℂ}
    (hK : IsKrausFamily K) : krausTransition K ∈ colStochastic ℝ n := by
  refine mem_colStochastic_iff_sum.mpr ⟨fun i j => ?_, fun j => ?_⟩
  · simp only [krausTransition, of_apply]
    positivity
  · have h := congrFun (congrFun hK j) j
    rw [Matrix.sum_apply, one_apply_eq] at h
    simp_rw [← sum_norm_sq_col_eq_conjTranspose_mul_self] at h
    apply Complex.ofReal_injective
    simp only [krausTransition, of_apply]
    rw [Finset.sum_comm]
    exact_mod_cast h

/-- Applied to a mixture of configurations `diag(p)`, the channel's output has diagonal
`Γ p`: the stochastic evolution of `p`. -/
theorem krausChannel_diagonal_apply_self (K : κ → Matrix n n ℂ) (p : n → ℝ) (i : n) :
    krausChannel K (diagonal fun j => (p j : ℂ)) i i = ((krausTransition K *ᵥ p) i : ℂ) := by
  have hk : ∀ k, (K k * diagonal (fun j => (p j : ℂ)) * (K k)ᴴ) i i =
      (((Matrix.of fun i j => ‖K k i j‖ ^ 2) *ᵥ p) i : ℂ) := fun k =>
    bornDensity_apply_self (fun _ _ => rfl) p i
  simp only [krausChannel, Matrix.sum_apply]
  rw [Finset.sum_congr rfl fun k _ => hk k]
  simp only [Matrix.mulVec, dotProduct, krausTransition, of_apply, Finset.sum_mul]
  push_cast
  exact Finset.sum_comm

/-- The "classical" Kraus operators of a stochastic matrix: `K (a, b) = √Γ_ab · |a⟩⟨b|`. -/
noncomputable def classicalKraus (Γ : Matrix n n ℝ) (c : n × n) : Matrix n n ℂ :=
  Matrix.of fun i j => if i = c.1 ∧ j = c.2 then (Real.sqrt (Γ c.1 c.2) : ℂ) else 0

/-- The classical Kraus operators of a stochastic matrix form a Kraus family. -/
theorem classicalKraus_isKrausFamily {Γ : Matrix n n ℝ} (hΓ : Γ ∈ colStochastic ℝ n) :
    IsKrausFamily (classicalKraus Γ) := by
  ext x y
  simp [classicalKraus, Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_prod_type, ite_and]
  by_cases hxy : x = y
  · subst hxy
    have h := sum_col_of_mem_colStochastic hΓ x
    simp [Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (nonneg_of_mem_colStochastic hΓ)]
    exact_mod_cast h
  · simp [hxy]

/-- Every stochastic matrix is the transition matrix of a quantum channel. -/
theorem krausTransition_classicalKraus {Γ : Matrix n n ℝ} (hΓ : Γ ∈ colStochastic ℝ n) :
    krausTransition (classicalKraus Γ) = Γ := by
  ext i j
  simp [krausTransition, classicalKraus, Fintype.sum_prod_type, ite_and,
    apply_ite (fun z : ℂ => ‖z‖ ^ 2), Complex.norm_real,
    Real.sq_sqrt (nonneg_of_mem_colStochastic hΓ)]

end ISM
