/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib

/-!
# Kronecker products of stochastic matrices

Candidate for upstreaming to Mathlib.

## Main results

* `Matrix.kronecker_mem_colStochastic`: the Kronecker product of two column-stochastic
  matrices is column-stochastic. Physically, two independent systems evolve by the product
  of their transition matrices.
-/

@[expose] public section

open Kronecker

namespace Matrix

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
  {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The Kronecker product of two column-stochastic matrices is column-stochastic. -/
theorem kronecker_mem_colStochastic {A : Matrix m m R} {B : Matrix n n R}
    (hA : A ∈ colStochastic R m) (hB : B ∈ colStochastic R n) :
    A ⊗ₖ B ∈ colStochastic R (m × n) := by
  refine mem_colStochastic_iff_sum.mpr ⟨fun i j => ?_, fun j => ?_⟩
  · exact mul_nonneg (nonneg_of_mem_colStochastic hA) (nonneg_of_mem_colStochastic hB)
  · simp only [kroneckerMap_apply, Fintype.sum_prod_type, ← Finset.mul_sum,
      sum_col_of_mem_colStochastic hA, sum_col_of_mem_colStochastic hB,
      mul_one]
end Matrix
