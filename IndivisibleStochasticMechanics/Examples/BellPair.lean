/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Quantum.Bell

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

* `corr_eq`, `chsh_bellCorr`, `lhv_corr_ne_bellCorr`: if Alice and Bob rotate their qubits
  locally and then read the configurations, the correlation is `cos 2(a - b)`; with the
  standard settings the CHSH value is `2√2`, so no local hidden-variable model reproduces
  these transition probabilities (Bell 1964; CHSH 1969).
* `chsh_pointerCorr`, `exists_apparatus_chsh`: the same value `2√2` for the pointers of
  local ideal apparatuses.

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


/-- The real rotation by `θ`. -/
noncomputable def rotR (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- The rotation by `θ`, as a complex matrix: a local change of basis on one qubit. -/
noncomputable def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (rotR θ).map (↑)

/-- Amplitudes after local rotations of the Bell pair. -/
theorem rot_kron_prep_apply (a b : ℝ) (i : Fin 2 × Fin 2) :
    ((rot a ⊗ₖ rot b) * prep) i (0, 0) =
      (((rotR a i.1 0 * rotR b i.2 0 + rotR a i.1 1 * rotR b i.2 1) / Real.sqrt 2 : ℝ) : ℂ) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [prep_col, Fin.sum_univ_two, kroneckerMap_apply, rot, map_apply]
  simp
  ring

/-- The outcome `+1` for configuration `0` and `-1` for `1`. -/
def sgn (i : Fin 2) : ℝ := if i = 0 then 1 else -1

/-- The Bell-pair correlation when Alice rotates by `a` and Bob by `b` and then both
configurations are read: `E = ∑ sgn(i₁) sgn(i₂) P(i₁, i₂)`, with `P` the transition
probabilities of the composite process. -/
noncomputable def corr (a b : ℝ) : ℝ :=
  ∑ i : Fin 2 × Fin 2, sgn i.1 * sgn i.2 * normSqMatrix ((rot a ⊗ₖ rot b) * prep) i (0, 0)

/-- **The Bell-pair correlation:** `E(a, b) = cos 2(a - b)`. -/
theorem corr_eq (a b : ℝ) : corr a b = Real.cos (2 * (a - b)) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2' : Real.sqrt 2 ≠ 0 := by positivity
  simp only [corr, normSqMatrix, of_apply, rot_kron_prep_apply, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Fintype.sum_prod_type, Fin.sum_univ_two, sgn, rotR]
  simp [Real.cos_two_mul, Real.cos_sub, div_pow, h2]
  field_simp
  linear_combination (-2 * (Real.sin b ^ 2 + Real.cos b ^ 2)) * Real.sin_sq_add_cos_sq a -
    2 * Real.sin_sq_add_cos_sq b

/-- Alice's settings `0, π/4` and Bob's `π/8, -π/8`. -/
noncomputable def alice : Fin 2 → ℝ := ![0, Real.pi / 4]

/-- Bob's settings. -/
noncomputable def bob : Fin 2 → ℝ := ![Real.pi / 8, -(Real.pi / 8)]

/-- The four correlations of the CHSH experiment on the Bell pair. -/
noncomputable def bellCorr (x y : Fin 2) : ℝ := corr (alice x) (bob y)

/-- **The Bell pair reaches Tsirelson's bound:** `S = 2√2`. -/
theorem chsh_bellCorr : chsh bellCorr = 2 * Real.sqrt 2 := by
  have h3 : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_four]
  simp only [chsh, bellCorr, corr_eq, alice, bob]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show 2 * (0 - Real.pi / 8) = -(Real.pi / 4) by ring,
    show 2 * (0 - -(Real.pi / 8)) = Real.pi / 4 by ring,
    show 2 * (Real.pi / 4 - Real.pi / 8) = Real.pi / 4 by ring,
    show 2 * (Real.pi / 4 - -(Real.pi / 8)) = 3 * Real.pi / 4 by ring,
    Real.cos_neg, Real.cos_pi_div_four, h3]
  ring

/-- **No local hidden-variable model reproduces the Bell-pair correlations** (Bell 1964;
CHSH 1969): they violate the CHSH inequality. -/
theorem lhv_corr_ne_bellCorr {Λ : Type*} [Fintype Λ] (L : LHVModel Λ) :
    L.corr ≠ bellCorr := by
  intro h
  have h1 := L.abs_chsh_corr_le_two
  rw [h, chsh_bellCorr, abs_of_pos (by positivity)] at h1
  have : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith


/-- Rotations are unitary. -/
theorem rot_mem_unitaryGroup (θ : ℝ) : rot θ ∈ unitaryGroup (Fin 2) ℂ := by
  have h : ((Real.cos θ : ℂ)) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  rw [mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, rotR, Matrix.mul_apply, Fin.sum_univ_two, Complex.conj_ofReal,
      -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    first | ring1 | linear_combination h

/-- **The Bell pair measured with apparatuses reaches `2√2`.** If Alice and Bob measure with
any ideal apparatuses (chapter 9) in the rotated bases, the pointers' CHSH value is `2√2`. -/
theorem chsh_pointerCorr {M : Fin 2 → Matrix (Fin 2 × Option (Fin 2)) (Fin 2 × Option (Fin 2)) ℂ}
    {N : Fin 2 → Matrix (Fin 2 × Option (Fin 2)) (Fin 2 × Option (Fin 2)) ℂ}
    (hM : ∀ x, IsIdealMeasurement (rot (alice x))ᴴ (M x))
    (hN : ∀ y, IsIdealMeasurement (rot (bob y))ᴴ (N y)) :
    chsh (pointerCorr M N prep (fun _ => sgn) (fun _ => sgn) (0, 0)) = 2 * Real.sqrt 2 := by
  rw [pointerCorr_eq hM hN (fun x => Unitary.star_mem (rot_mem_unitaryGroup _))
    (fun y => Unitary.star_mem (rot_mem_unitaryGroup _))]
  simp only [conjTranspose_conjTranspose]
  exact chsh_bellCorr

/-- Such apparatuses exist. -/
theorem exists_apparatus_chsh :
    ∃ M N : Fin 2 → Matrix (Fin 2 × Option (Fin 2)) (Fin 2 × Option (Fin 2)) ℂ,
      (∀ x, IsIdealMeasurement (rot (alice x))ᴴ (M x)) ∧
      (∀ y, IsIdealMeasurement (rot (bob y))ᴴ (N y)) ∧
      chsh (pointerCorr M N prep (fun _ => sgn) (fun _ => sgn) (0, 0)) = 2 * Real.sqrt 2 := by
  choose M hM using fun x => exists_isIdealMeasurement
    (Unitary.star_mem (rot_mem_unitaryGroup (alice x)))
  choose N hN using fun y => exists_isIdealMeasurement
    (Unitary.star_mem (rot_mem_unitaryGroup (bob y)))
  exact ⟨M, N, hM, hN, chsh_pointerCorr hM hN⟩

end ISM.BellPair
