/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib

/-!
# Completing orthonormal columns to a unitary matrix

Candidate for upstreaming to Mathlib.

## Main results

* `Matrix.exists_mem_unitaryGroup_of_orthonormal`: a family of orthonormal vectors in
  `EuclideanSpace 𝕜 ι`, indexed by a subset `s ⊆ ι`, extends to a unitary matrix whose
  columns at the indices in `s` are the given vectors.
-/

@[expose] public section

open Module

namespace Matrix

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- Orthonormal columns, indexed by a subset `s`, can be completed to a unitary matrix. -/
theorem exists_mem_unitaryGroup_of_orthonormal {s : Set ι} {v : ι → EuclideanSpace 𝕜 ι}
    (hv : Orthonormal 𝕜 (s.domRestrict v)) :
    ∃ U ∈ unitaryGroup ι 𝕜, ∀ j ∈ s, ∀ i, U i j = v j i := by
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq finrank_euclideanSpace
  refine ⟨(EuclideanSpace.basisFun ι 𝕜).toBasis.toMatrix b,
    (EuclideanSpace.basisFun ι 𝕜).toMatrix_orthonormalBasis_mem_unitary b, fun j hj i => ?_⟩
  simp [Basis.toMatrix_apply, hb j hj]

end Matrix

namespace Matrix

variable {m n : Type*} [Fintype m]

/-- The squared norm of the `j`-th column of a complex matrix is the `(j, j)` entry of `Aᴴ * A`. -/
theorem sum_norm_sq_col_eq_conjTranspose_mul_self (A : Matrix m n ℂ) (j : n) :
    ((∑ i, ‖A i j‖ ^ 2 : ℝ) : ℂ) = (Aᴴ * A) j j := by
  push_cast
  simp only [Matrix.mul_apply, conjTranspose_apply, Complex.star_def]
  exact Finset.sum_congr rfl fun i _ => (Complex.conj_mul' (A i j)).symm

/-- A unitary matrix preserves the squared Euclidean norm: `∑ e, ‖(B x) e‖² = ∑ e, ‖x e‖²`. -/
theorem sum_norm_sq_mulVec_of_mem_unitaryGroup [DecidableEq m] {B : Matrix m m ℂ}
    (hB : B ∈ unitaryGroup m ℂ) (x : m → ℂ) :
    ∑ e, ‖(B *ᵥ x) e‖ ^ 2 = ∑ e, ‖x e‖ ^ 2 := by
  have key : ∀ y : m → ℂ, ((∑ e, ‖y e‖ ^ 2 : ℝ) : ℂ) = star y ⬝ᵥ y := fun y => by
    push_cast; simp [dotProduct, Complex.mul_conj', mul_comm]
  apply Complex.ofReal_injective
  rw [key, key, star_mulVec, dotProduct_mulVec, vecMul_vecMul]
  rw [show Bᴴ * B = 1 from mem_unitaryGroup_iff'.mp hB, vecMul_one]

end Matrix
