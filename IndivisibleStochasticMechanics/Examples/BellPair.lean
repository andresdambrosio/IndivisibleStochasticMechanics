/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Quantum.Composite

/-!
# A Bell pair, seen from the stochastic side

Two qubits start in the configuration `(0, 0)`. A Hadamard on the first and a CNOT prepare
the Bell state `(|00⟩ + |11⟩)/√2`. In stochastic language:

* `normSq_prep`: right after the preparation the qubits agree: `(0,0)` or `(1,1)`, each
  with probability `1/2`.
* `not_product`: this joint distribution is not a product. The qubits are correlated.
* `coherent`: after a further Hadamard on *each* qubit (a local change of basis), they
  still agree with certainty.
* `decohered`, `decohered_of_isRecording`: if the preparation is followed by a division
  event (an environment that records the configuration), the same local Hadamards give the
  uniform distribution `1/4`.

At the intermediate time both histories have exactly the same configuration statistics.
What tells them apart is whether that time is a division event. That is how entanglement
shows up in the indivisible stochastic picture: correlations together with the absence of
a division event. The quantum facts used here (the Bell state and its invariance under
`H ⊗ H`) are textbook material; the stochastic reading follows Barandes.

## References

* J. A. Barandes, *The Stochastic-Quantum Correspondence*, arXiv:2302.10778, §3.9.
* M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*
  (Cambridge, 2000), §1.3.6 (Bell states).
-/

@[expose] public section

open Matrix Kronecker

namespace ISM.BellPair


/-- The Hadamard gate `(1/√2) [[1, 1], [1, -1]]`. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / (Real.sqrt 2 : ℂ), 1 / (Real.sqrt 2 : ℂ); 1 / (Real.sqrt 2 : ℂ), -1 / (Real.sqrt 2 : ℂ)]

/-- The controlled-NOT gate: `|a, b⟩ ↦ |a, b + a⟩` (addition mod 2). -/
def cnot : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun i j => if i = (j.1, j.2 + j.1) then 1 else 0

/-- Bell-pair preparation: a Hadamard on the first qubit, then a CNOT. -/
noncomputable def prep : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  cnot * (hadamard ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))

/-- `|1/√2|² = 1/2`. -/
theorem sq_inv_sqrt_two : ‖1 / (Real.sqrt 2 : ℂ)‖ ^ 2 = 1 / 2 := by
  rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), div_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- From `|00⟩`, the preparation gives the Bell state `(|00⟩ + |11⟩)/√2`. -/
theorem prep_col (i : Fin 2 × Fin 2) :
    prep i (0, 0) = if i.1 = i.2 then 1 / (Real.sqrt 2 : ℂ) else 0 := by
  obtain ⟨a, b⟩ := i
  fin_cases a <;> fin_cases b <;>
    simp [prep, cnot, hadamard, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.one_apply]

/-- After the preparation the two qubits agree, each value with probability `1/2`. -/
theorem normSq_prep (i : Fin 2 × Fin 2) :
    normSqMatrix prep i (0, 0) = if i.1 = i.2 then 1 / 2 else 0 := by
  simp only [normSqMatrix, of_apply, prep_col]
  split_ifs <;> simp

/-- Every entry of `|H|²` is `1/2`. -/
theorem normSq_hadamard (a b : Fin 2) : normSqMatrix hadamard a b = 1 / 2 := by
  fin_cases a <;> fin_cases b <;> simp [normSqMatrix, hadamard]

/-- The Bell state is invariant under `H ⊗ H`. -/
theorem hadamard_kronecker_mul_prep (i : Fin 2 × Fin 2) :
    ((hadamard ⊗ₖ hadamard) * prep) i (0, 0) = prep i (0, 0) := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hs : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hx : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, hs, one_div]
  obtain ⟨a, b⟩ := i
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, prep_col,
    kroneckerMap_apply]
  fin_cases a <;> fin_cases b <;> simp [hadamard] <;>
    first | ring1 | linear_combination (2 * (Real.sqrt 2 : ℂ)⁻¹) * hx

/-- **Without a division event the correlations survive a change of basis.** After local
Hadamards on both qubits, the qubits still agree with certainty. -/
theorem coherent (i : Fin 2 × Fin 2) :
    normSqMatrix ((hadamard ⊗ₖ hadamard) * prep) i (0, 0) = if i.1 = i.2 then 1 / 2 else 0 := by
  rw [← normSq_prep]
  simp only [normSqMatrix, of_apply, hadamard_kronecker_mul_prep]

/-- **The two qubits are correlated:** the joint distribution after the preparation is not
a product `p ⊗ q`. -/
theorem not_product :
    ¬ ∃ p q : Fin 2 → ℝ, ∀ i, normSqMatrix prep i (0, 0) = p i.1 * q i.2 := by
  rintro ⟨p, q, h⟩
  have h00 := h (0, 0); have h01 := h (0, 1); have h10 := h (1, 0); have h11 := h (1, 1)
  simp only [normSq_prep] at h00 h01 h10 h11
  norm_num at h00 h01 h10 h11
  rcases h01 with h | h
  · simp [h] at h00
  · simp [h] at h11

/-- With a division event right after the preparation, local Hadamards give the uniform
distribution `1/4`. -/
theorem decohered (i : Fin 2 × Fin 2) :
    (normSqMatrix (hadamard ⊗ₖ hadamard) * normSqMatrix prep) i (0, 0) = 1 / 4 := by
  rw [normSqMatrix_kronecker]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, normSq_prep,
    kroneckerMap_apply, normSq_hadamard]
  norm_num

/-- **A decohering environment destroys the Bell correlations.** If any environment records
the two-qubit configuration perfectly right after the preparation, the same local Hadamards
give the uniform distribution. Nobody needs to read the record. -/
theorem decohered_of_isRecording {m : Type*} [Fintype m] [DecidableEq m]
    {φ : Fin 2 × Fin 2 → m → ℂ} {E : Matrix ((Fin 2 × Fin 2) × m) ((Fin 2 × Fin 2) × m) ℂ}
    {e₀ : m} (hE : IsRecording φ E e₀) (hφ : ∀ k l, overlap φ k l = if k = l then 1 else 0)
    (i : Fin 2 × Fin 2) :
    envMarginal (recordedEvolution (hadamard ⊗ₖ hadamard) E prep) e₀ i (0, 0) = 1 / 4 := by
  rw [hE.envMarginal_of_orthonormal hφ]
  exact decohered i

end ISM.BellPair
