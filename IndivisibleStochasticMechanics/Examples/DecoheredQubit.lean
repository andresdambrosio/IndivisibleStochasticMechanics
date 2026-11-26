/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Examples.Qubit
public import IndivisibleStochasticMechanics.Quantum.Decoherence

/-!
# Partial decoherence of the qubit

The qubit of `ISM.Qubit` evolves under `H = σₓ`. At `π/4` an environment qubit records its
configuration *imperfectly*: configuration `0` leaves the record `(1, 0)` and configuration
`1` leaves `(cos θ, sin θ)`. The overlap of the two records is `cos θ`.

* `θ = π/2`: perfect record. `θ = 0`: no record at all.
* `decoheredProcess_swap`: the probability that the qubit has swapped at `π/2` is
  `(1 + cos θ) / 2`. It goes from `1` (coherent, a deterministic swap) to `1/2` (fully
  decohered).
* `decoheredProcess_isDivisionEvent_iff`: `π/4` is a division event **if and only if** the
  record is perfect, `cos θ = 0`. A partial record is not enough.
-/

@[expose] public section

open Matrix Complex

namespace ISM.Qubit

/-- The qubit evolution is a one-parameter group: `U s U(t)† = U (s - t)`. -/
theorem U_mul_conjTranspose (s t : ℝ) : U s * (U t)ᴴ = U (s - t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U, Matrix.mul_apply, Fin.sum_univ_two, -Complex.ofReal_cos, -Complex.ofReal_sin,
      Real.cos_sub, Real.sin_sub] <;> push_cast <;> ring_nf <;> simp [Complex.I_sq]

/-- The environment's record of the qubit: `(1, 0)` for configuration `0` and
`(cos θ, sin θ)` for configuration `1`. -/
noncomputable def recordState (θ : ℝ) : Fin 2 → Fin 2 → ℂ :=
  ![![1, 0], ![(Real.cos θ : ℂ), (Real.sin θ : ℂ)]]

/-- Both records are unit vectors. -/
theorem recordState_unit (θ : ℝ) (j : Fin 2) : ∑ e, ‖recordState θ j e‖ ^ 2 = 1 := by
  fin_cases j <;> simp [recordState, Fin.sum_univ_two, Complex.norm_real, Real.cos_sq_add_sin_sq,
    -Complex.ofReal_cos, -Complex.ofReal_sin]

/-- The overlap of the two records is `cos θ`. -/
theorem overlap_recordState (θ : ℝ) (k l : Fin 2) :
    overlap (recordState θ) k l = if k = l then 1 else (Real.cos θ : ℂ) := by
  have h : (Real.cos θ : ℂ) * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
    exact_mod_cast (by nlinarith [Real.cos_sq_add_sin_sq θ] :
      Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1)
  fin_cases k <;> fin_cases l <;>
    simp [overlap, recordState, Fin.sum_univ_two, -Complex.ofReal_cos, -Complex.ofReal_sin, h]

/-- A recording interaction exists for every `θ`. -/
theorem exists_isRecording_recordState (θ : ℝ) :
    ∃ E, IsRecording (recordState θ) E 0 :=
  exists_isRecording (recordState_unit θ) 0

/-- A unitary that records the qubit with the records `recordState θ`. -/
noncomputable def recorder (θ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (exists_isRecording_recordState θ).choose

/-- `recorder θ` records with `recordState θ`. -/
theorem recorder_spec (θ : ℝ) : IsRecording (recordState θ) (recorder θ) 0 :=
  (exists_isRecording_recordState θ).choose_spec

/-- The qubit process with an environment recording it, with overlap `cos θ`, at `π/4`. -/
noncomputable def decoheredProcess (θ : ℝ) : GenStochasticProcess (Fin 2) :=
  GenStochasticProcess.recordedAt U U_mem_unitaryGroup U_zero (recorder θ) (recorder_spec θ).1 0
    (Real.pi / 4) (by positivity)

/-- The decoherence formula at `π/2`. -/
theorem decoheredProcess_Γ_pi_div_two (θ : ℝ) (i j : Fin 2) :
    ((decoheredProcess θ).Γ (Real.pi / 2) i j : ℂ) =
      ∑ k, ∑ l, U (Real.pi / 4) i k * U (Real.pi / 4) k j *
        star (U (Real.pi / 4) i l * U (Real.pi / 4) l j) * overlap (recordState θ) k l := by
  rw [decoheredProcess, GenStochasticProcess.recordedAt_Γ_of_le (by linarith [Real.pi_pos]),
    U_mul_conjTranspose, (recorder_spec θ).envMarginal_recordedEvolution]
  ring_nf

/-- The probability of a swap at `π/2` is `(1 + cos θ) / 2`. -/
theorem decoheredProcess_swap (θ : ℝ) :
    (decoheredProcess θ).Γ (Real.pi / 2) 1 0 = (1 + Real.cos θ) / 2 := by
  apply Complex.ofReal_injective
  rw [decoheredProcess_Γ_pi_div_two]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  simp [Fin.sum_univ_two, overlap_recordState, U, -Complex.ofReal_cos, -Complex.ofReal_sin]
  ring_nf
  simp [Complex.I_sq, h2, map_ofNat]
  ring

/-- The probability of staying in `1` at `π/2` is `(1 - cos θ) / 2`. -/
theorem decoheredProcess_stay (θ : ℝ) :
    (decoheredProcess θ).Γ (Real.pi / 2) 1 1 = (1 - Real.cos θ) / 2 := by
  apply Complex.ofReal_injective
  rw [decoheredProcess_Γ_pi_div_two]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  simp [Fin.sum_univ_two, overlap_recordState, U, -Complex.ofReal_cos, -Complex.ofReal_sin]
  ring_nf
  simp [Complex.I_sq, h2, map_ofNat]
  ring

/-- At `π/4`, the qubit is completely mixed, whatever the record. -/
theorem decoheredProcess_Γ_pi_div_four (θ : ℝ) (i j : Fin 2) :
    (decoheredProcess θ).Γ (Real.pi / 4) i j = 1 / 2 := by
  rw [decoheredProcess, GenStochasticProcess.recordedAt_Γ_at (recorder_spec θ)
    (recordState_unit θ)]
  have h := congrFun (congrFun (process_Γ (Real.pi / 4)) i) j
  simp only [process, GenStochasticProcess.ofUnitary_Γ_apply] at h
  have h2 : (Real.sqrt 2 / 2) ^ 2 = 2⁻¹ := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [normSqMatrix, of_apply, h]
  fin_cases i <;> fin_cases j <;> simp [h2]

/-- **Partial decoherence does not divide.** `π/4` is a division event if and only if the
environment records the configuration perfectly. -/
theorem decoheredProcess_isDivisionEvent_iff (θ : ℝ) :
    (decoheredProcess θ).IsDivisionEvent (Real.pi / 4) ↔ Real.cos θ = 0 := by
  constructor
  · rintro ⟨-, Δ, hΔ⟩
    have h := (hΔ (Real.pi / 2) (by linarith [Real.pi_pos])).2
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simp only [Matrix.mul_apply, decoheredProcess_Γ_pi_div_four] at h10 h11
    rw [decoheredProcess_swap] at h10
    rw [decoheredProcess_stay] at h11
    linarith
  · intro hc
    refine GenStochasticProcess.recordedAt_isDivisionEvent (recorder_spec θ) fun k l => ?_
    rw [overlap_recordState, hc]
    split_ifs <;> simp

end ISM.Qubit
