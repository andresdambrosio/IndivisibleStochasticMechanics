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
