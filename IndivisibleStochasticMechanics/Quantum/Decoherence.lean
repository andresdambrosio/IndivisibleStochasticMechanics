/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Quantum.Collapse
public import IndivisibleStochasticMechanics.Stochastic.ApproxDivision

/-!
# Decoherence: an environment that records creates division events

In `ISM.Quantum.Collapse` an *apparatus* measured the system. Nothing in that argument used
that someone reads the pointer. Here the apparatus is replaced by a generic **environment**
(any finite configuration space `m`, prepared in `e₀`) that *records* the system's
configuration: `|k⟩ ⊗ |e₀⟩ ↦ |k⟩ ⊗ |φ_k⟩`. The record states `φ_k` are unit vectors,
but they need not be orthogonal. The record may be imperfect.

The system evolves by `U`, is recorded, and then evolves by `W`. Its transition
probabilities, summing over the environment, are

  `Γ i j = ∑ k, ∑ l, W i k U k j · conj(W i l U l j) · ⟨φ_l, φ_k⟩`.

* **Perfect record** (`φ_k` orthonormal): only `k = l` survives, so `Γ = |W|² · |U|²`, and the
  recording time is a **division event** for any unitary dynamics.
* **No record** (all `φ_k` equal): `Γ = |W U|²`, the coherent evolution.
* **Partial record:** the interference terms are weighted by the overlaps `⟨φ_l, φ_k⟩`.
  Decoherence interpolates continuously between the two.

No one has to look at the environment. Division events, and therefore "collapse", come
from the physical correlation between system and environment.

## Main definitions

* `ISM.IsRecording φ E e₀`: `E` is a unitary on system ⊗ environment that records the
  configuration `k` in the environment state `φ k`.
* `ISM.overlap φ k l = ∑ e, φ k e · conj (φ l e)`: the overlap of two records.
* `ISM.recordedEvolution W E U`: evolve by `U`, record with `E`, evolve by `W`.
* `ISM.envMarginal Θ e₀`: the system's transition matrix, summing over the environment.
* `ISM.GenStochasticProcess.recordedAt`: the system's process when an environment records its
  configuration at time `t₁`.

## Main results

* `ISM.exists_isRecording`: every family of unit record states is realized by a unitary.
* `ISM.IsRecording.envMarginal_recordedEvolution`: the decoherence formula above.
* `ISM.IsRecording.envMarginal_of_orthonormal`: perfect record ⇒ `Γ = |W|² · |U|²`.
* `ISM.IsRecording.envMarginal_of_const`: no record ⇒ `Γ = |W U|²`.
* `ISM.GenStochasticProcess.recordedAt_isDivisionEvent`: a perfect record at `t₁` makes `t₁`
  a division event.
* `ISM.GenStochasticProcess.recordedAt_divisionDefect_le`: an imperfect record, with
  overlaps at most `ε`, makes `t₁` an approximate division event: its division defect
  (`ISM.GenStochasticProcess.divisionDefect`) is at most `(N - 1) ε / 2`. This quantitative
  statement is original to this project.

## References

* J. A. Barandes, *The Stochastic-Quantum Correspondence*, arXiv:2302.10778
  (decoherence and division events).
* W. H. Zurek, *Decoherence, einselection, and the quantum origins of the classical*,
  Rev. Mod. Phys. 75, 715 (2003).
-/

@[expose] public section

open Matrix Kronecker

namespace ISM

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- `E` *records* the configuration of the system in the environment: with the environment
in `e₀`, `E (|j⟩ ⊗ |e₀⟩) = |j⟩ ⊗ |φ j⟩`. The system's configuration is left
unchanged. -/
def IsRecording (φ : n → m → ℂ) (E : Matrix (n × m) (n × m) ℂ) (e₀ : m) : Prop :=
  E ∈ unitaryGroup (n × m) ℂ ∧ ∀ i e j, E (i, e) (j, e₀) = if i = j then φ j e else 0

/-- The overlap `⟨φ_l, φ_k⟩ = ∑ e, φ k e · conj (φ l e)` of two records. It measures how
well the environment fails to tell `k` from `l`. -/
def overlap (φ : n → m → ℂ) (k l : n) : ℂ := ∑ e, φ k e * star (φ l e)

/-- Auxiliary: the columns `|j⟩ ⊗ |φ j⟩` of a recording unitary. -/
noncomputable def recordingVec (φ : n → m → ℂ) (c : n × m) : EuclideanSpace ℂ (n × m) :=
  WithLp.toLp 2 fun x => if x.1 = c.1 then φ c.1 x.2 else 0

/-- The columns `|j⟩ ⊗ |φ j⟩` are orthonormal whenever each record is a unit vector:
the system part alone keeps different `j` orthogonal. -/
theorem recordingVec_orthonormal {φ : n → m → ℂ} (hφ : ∀ j, ∑ e, ‖φ j e‖ ^ 2 = 1)
    (e₀ : m) :
    Orthonormal ℂ ({c : n × m | c.2 = e₀}.domRestrict (recordingVec φ)) := by
  rw [orthonormal_iff_ite]
  rintro ⟨⟨j, _⟩, hj⟩ ⟨⟨k, _⟩, hk⟩
  simp only [Set.mem_ofPred_eq] at hj hk
  subst hj hk
  simp only [Set.domRestrict_apply, PiLp.inner_apply]
  simp only [recordingVec, Fintype.sum_prod_type]
  by_cases hjk : j = k
  · subst hjk
    simp [apply_ite (fun z : ℂ => (‖z‖ : ℂ) ^ 2)]
    exact_mod_cast hφ j
  · simp [hjk, Ne.symm hjk]

/-- Every family of unit record states is realized by a unitary interaction. -/
theorem exists_isRecording {φ : n → m → ℂ} (hφ : ∀ j, ∑ e, ‖φ j e‖ ^ 2 = 1)
    (e₀ : m) :
    ∃ E, IsRecording φ E e₀ := by
  obtain ⟨E, hE, hEv⟩ :=
    exists_mem_unitaryGroup_of_orthonormal (recordingVec_orthonormal hφ e₀)
  refine ⟨E, hE, fun i e j => ?_⟩
  rw [hEv (j, e₀) rfl]
  simp [recordingVec]

/-- Evolve the system by `U`, record it with `E`, then evolve the system by `W`. The
environment does not move outside the recording. -/
def recordedEvolution (W : Matrix n n ℂ) (E : Matrix (n × m) (n × m) ℂ) (U : Matrix n n ℂ) :
    Matrix (n × m) (n × m) ℂ :=
  (W ⊗ₖ (1 : Matrix m m ℂ)) * (E * (U ⊗ₖ (1 : Matrix m m ℂ)))

/-- The system's transition matrix from a composite evolution `Θ`, summing over the final
environment configuration, with the environment initially in `e₀`. -/
noncomputable def envMarginal (Θ : Matrix (n × m) (n × m) ℂ) (e₀ : m) : Matrix n n ℝ :=
  Matrix.of fun i j => ∑ e, ‖Θ (i, e) (j, e₀)‖ ^ 2

/-- The composite amplitude: `∑ k, W i k · U k j · φ k e`. -/
theorem IsRecording.recordedEvolution_apply {φ : n → m → ℂ}
    {E : Matrix (n × m) (n × m) ℂ}
    {e₀ : m} (hE : IsRecording φ E e₀) (W U : Matrix n n ℂ) (i : n) (e : m) (j : n) :
    recordedEvolution W E U (i, e) (j, e₀) = ∑ k, W i k * U k j * φ k e := by
  rw [recordedEvolution, kron_one_mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, kroneckerMap_apply, Matrix.one_apply]
  simp [hE.2, mul_comm, mul_left_comm]

omit [DecidableEq n] [DecidableEq m] in
/-- `∑ e, |∑ k, a k φ k e|² = ∑ k l, a k · conj (a l) · ⟨φ_l, φ_k⟩`. -/
theorem sum_normSq_sum_eq (a : n → ℂ) (φ : n → m → ℂ) :
    ((∑ e, ‖∑ k, a k * φ k e‖ ^ 2 : ℝ) : ℂ) =
      ∑ k, ∑ l, a k * star (a l) * overlap φ k l := by
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, map_mul, Finset.sum_mul_sum, overlap, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun e _ => ?_
  simp only [Complex.star_def]; ring

/-- **The decoherence formula.** The interference term between `k` and `l` is weighted by the
overlap of their records. -/
theorem IsRecording.envMarginal_recordedEvolution {φ : n → m → ℂ}
    {E : Matrix (n × m) (n × m) ℂ} {e₀ : m} (hE : IsRecording φ E e₀)
    (W U : Matrix n n ℂ) (i j : n) :
    (envMarginal (recordedEvolution W E U) e₀ i j : ℂ) =
      ∑ k, ∑ l, W i k * U k j * star (W i l * U l j) * overlap φ k l := by
  simp only [envMarginal, of_apply, hE.recordedEvolution_apply]
  exact sum_normSq_sum_eq _ φ

/-- **Perfect record.** If the records are orthonormal, interference disappears:
`Γ = |W|² · |U|²`. -/
theorem IsRecording.envMarginal_of_orthonormal {φ : n → m → ℂ}
    {E : Matrix (n × m) (n × m) ℂ} {e₀ : m} (hE : IsRecording φ E e₀)
    (hφ : ∀ k l, overlap φ k l = if k = l then 1 else 0) (W U : Matrix n n ℂ) :
    envMarginal (recordedEvolution W E U) e₀ = normSqMatrix W * normSqMatrix U := by
  ext i j
  apply Complex.ofReal_injective
  rw [hE.envMarginal_recordedEvolution]
  simp only [hφ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Matrix.mul_apply, normSqMatrix, of_apply]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.mul_conj', ← Complex.mul_conj']
  simp only [Complex.star_def, map_mul]; ring

/-- **No record.** If every configuration leaves the same record, the evolution is the
coherent one: `Γ = |W U|²`. -/
theorem IsRecording.envMarginal_of_const {ψ : m → ℂ} (hψ : ∑ e, ‖ψ e‖ ^ 2 = 1)
    {E : Matrix (n × m) (n × m) ℂ} {e₀ : m} (hE : IsRecording (fun _ : n => ψ) E e₀)
    (W U : Matrix n n ℂ) :
    envMarginal (recordedEvolution W E U) e₀ = normSqMatrix (W * U) := by
  have h1 : ∀ k l : n, overlap (fun _ : n => ψ) k l = (1 : ℂ) := fun k l => by
    simp only [overlap, Complex.star_def, Complex.mul_conj']; exact_mod_cast hψ
  ext i j
  apply Complex.ofReal_injective
  rw [hE.envMarginal_recordedEvolution]
  simp only [h1, mul_one, normSqMatrix, of_apply, Matrix.mul_apply]
  push_cast
  rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  simp only [Complex.star_def, map_mul]

/-- Recording does not change the probabilities at the moment it happens. -/
theorem IsRecording.envMarginal_recordedEvolution_one {φ : n → m → ℂ}
    {E : Matrix (n × m) (n × m) ℂ} {e₀ : m} (hE : IsRecording φ E e₀)
    (hφ : ∀ j, ∑ e, ‖φ j e‖ ^ 2 = 1) (U : Matrix n n ℂ) :
    envMarginal (recordedEvolution 1 E U) e₀ = normSqMatrix U := by
  ext i j
  simp only [envMarginal, of_apply, hE.recordedEvolution_apply, Matrix.one_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, norm_mul, mul_pow,
    normSqMatrix]
  rw [← Finset.mul_sum, hφ, mul_one]

omit [Fintype n] [DecidableEq n] in
/-- Without a recording, the system marginal of `A ⊗ 1` is `|A|²`. -/
theorem envMarginal_kron_one (A : Matrix n n ℂ) (e₀ : m) :
    envMarginal (A ⊗ₖ (1 : Matrix m m ℂ)) e₀ = normSqMatrix A := by
  ext i j
  simp [envMarginal, normSqMatrix, Matrix.one_apply, apply_ite (fun z : ℂ => ‖z‖ ^ 2)]

/-- **Approximate decoherence, entrywise.** Replacing the true transition probabilities by
the fully decohered ones `|W|² |U|²` costs at most `ε ∑_{k ≠ l} aₖ aₗ`, with
`aₖ = |Wᵢₖ| |Uₖⱼ|`, where `ε` bounds the overlaps of distinct records. -/
theorem IsRecording.abs_envMarginal_sub_le {φ : n → m → ℂ} {E : Matrix (n × m) (n × m) ℂ}
    {e₀ : m} (hE : IsRecording φ E e₀) (hunit : ∀ j, ∑ e, ‖φ j e‖ ^ 2 = 1) {ε : ℝ}
    (hε : ∀ k l, k ≠ l → ‖overlap φ k l‖ ≤ ε) (W U : Matrix n n ℂ) (i j : n) :
    |envMarginal (recordedEvolution W E U) e₀ i j - (normSqMatrix W * normSqMatrix U) i j| ≤
      ε * ((∑ k, ‖W i k‖ * ‖U k j‖) ^ 2 - ∑ k, (‖W i k‖ * ‖U k j‖) ^ 2) := by
  have hkk : ∀ k, overlap φ k k = 1 := fun k => by
    simp only [overlap, Complex.star_def, Complex.mul_conj']
    exact_mod_cast hunit k
  have hdiff : ((envMarginal (recordedEvolution W E U) e₀ i j -
      (normSqMatrix W * normSqMatrix U) i j : ℝ) : ℂ) =
      ∑ k, ∑ l, if k = l then 0 else
        W i k * U k j * star (W i l * U l j) * overlap φ k l := by
    rw [Complex.ofReal_sub, hE.envMarginal_recordedEvolution]
    have hd : (((normSqMatrix W * normSqMatrix U) i j : ℝ) : ℂ) =
        ∑ k, ∑ l, if k = l then W i k * U k j * star (W i l * U l j) * overlap φ k l
          else 0 := by
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, hkk, mul_one]
      simp only [normSqMatrix, Matrix.mul_apply, of_apply]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.star_def, Complex.mul_conj', norm_mul]
      push_cast
      ring
    rw [hd, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> ring
  have hid : (∑ k, ‖W i k‖ * ‖U k j‖) ^ 2 - ∑ k, (‖W i k‖ * ‖U k j‖) ^ 2 =
      ∑ k, ∑ l, if k = l then 0 else ‖W i k‖ * ‖U k j‖ * (‖W i l‖ * ‖U l j‖) := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ∀ l, (if k = l then (0 : ℝ) else ‖W i k‖ * ‖U k j‖ * (‖W i l‖ * ‖U l j‖)) =
        ‖W i k‖ * ‖U k j‖ * (‖W i l‖ * ‖U l j‖) -
          if k = l then ‖W i k‖ * ‖U k j‖ * (‖W i l‖ * ‖U l j‖) else 0 := fun l => by
      split_ifs <;> ring
    simp_rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true, sq]
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hdiff, hid, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  split_ifs with hkl
  · simp
  · simp only [norm_mul, norm_star]
    have := hε k l hkl
    have h1 : 0 ≤ ‖W i k‖ * ‖U k j‖ * (‖W i l‖ * ‖U l j‖) := by positivity
    nlinarith

/-- Composite evolution when the system evolves by `U t` and an environment records its
configuration at `t₁`. -/
noncomputable def recordedComposite (U : ℝ → Matrix n n ℂ) (E : Matrix (n × m) (n × m) ℂ)
    (t₁ t : ℝ) : Matrix (n × m) (n × m) ℂ :=
  if t < t₁ then U t ⊗ₖ (1 : Matrix m m ℂ)
  else recordedEvolution (U t * (U t₁)ᴴ) E (U t₁)

theorem recordedComposite_mem_unitaryGroup {U : ℝ → Matrix n n ℂ}
    (hU : ∀ t, U t ∈ unitaryGroup n ℂ) {E : Matrix (n × m) (n × m) ℂ}
    (hE : E ∈ unitaryGroup (n × m) ℂ) (t₁ t : ℝ) :
    recordedComposite U E t₁ t ∈ unitaryGroup (n × m) ℂ := by
  have hk : ∀ A, A ∈ unitaryGroup n ℂ →
      A ⊗ₖ (1 : Matrix m m ℂ) ∈ unitaryGroup (n × m) ℂ :=
    fun A hA => kronecker_mem_unitary hA (one_mem _)
  unfold recordedComposite recordedEvolution
  split_ifs
  · exact hk _ (hU t)
  · exact mul_mem (hk _ (mul_mem (hU t) (Unitary.star_mem (hU t₁))))
      (mul_mem hE (hk _ (hU t₁)))

namespace GenStochasticProcess

/-- The system's generalized stochastic process when it evolves by `U t` and an environment
records its configuration (via `E`) at time `t₁ > 0`. -/
noncomputable def recordedAt (U : ℝ → Matrix n n ℂ) (hU : ∀ t, U t ∈ unitaryGroup n ℂ)
    (h0 : U 0 = 1) (E : Matrix (n × m) (n × m) ℂ) (hE : E ∈ unitaryGroup (n × m) ℂ)
    (e₀ : m) (t₁ : ℝ) (ht₁ : 0 < t₁) : GenStochasticProcess n where
  Γ t := envMarginal (recordedComposite U E t₁ t) e₀
  stochastic t _ :=
    IsUnitaryDilation.mem_colStochastic ⟨recordedComposite_mem_unitaryGroup hU hE t₁ t,
      fun _ _ => rfl⟩
  init := by
    rw [recordedComposite, ite_eq_left_of_eq_true _ _ (eq_true ht₁), envMarginal_kron_one, h0,
      normSqMatrix_one]

variable {U : ℝ → Matrix n n ℂ} {hU : ∀ t, U t ∈ unitaryGroup n ℂ} {h0 : U 0 = 1}
  {E : Matrix (n × m) (n × m) ℂ} {hE : E ∈ unitaryGroup (n × m) ℂ} {e₀ : m}
  {t₁ : ℝ} {ht₁ : 0 < t₁}

/-- After the recording, `Γ(t)` is the marginal of evolve–record–evolve. -/
theorem recordedAt_Γ_of_le {t : ℝ} (ht : t₁ ≤ t) :
    (recordedAt U hU h0 E hE e₀ t₁ ht₁).Γ t =
      envMarginal (recordedEvolution (U t * (U t₁)ᴴ) E (U t₁)) e₀ := by
  simp only [recordedAt, recordedComposite, not_lt.mpr ht, ite_false]

/-- At the recording time, `Γ(t₁) = |U(t₁)|²`. -/
theorem recordedAt_Γ_at {φ : n → m → ℂ} (hEφ : IsRecording φ E e₀)
    (hφ : ∀ j, ∑ e, ‖φ j e‖ ^ 2 = 1) :
    (recordedAt U hU h0 E hE e₀ t₁ ht₁).Γ t₁ = normSqMatrix (U t₁) := by
  have h : U t₁ * (U t₁)ᴴ = 1 := mem_unitaryGroup_iff.mp (hU t₁)
  rw [recordedAt_Γ_of_le le_rfl, h, hEφ.envMarginal_recordedEvolution_one hφ]

/-- **Decoherence creates division events.** If an environment records the configuration
perfectly at `t₁ > 0`, then `t₁` is a division event, whatever the unitary dynamics. No one
needs to read the record. -/
theorem recordedAt_isDivisionEvent {φ : n → m → ℂ} (hEφ : IsRecording φ E e₀)
    (hφ : ∀ k l, overlap φ k l = if k = l then 1 else 0) :
    (recordedAt U hU h0 E hE e₀ t₁ ht₁).IsDivisionEvent t₁ := by
  have hunit : ∀ j, ∑ e, ‖φ j e‖ ^ 2 = 1 := fun j => by
    have := hφ j j
    simp only [overlap, Complex.star_def, Complex.mul_conj', ite_true] at this
    exact_mod_cast this
  refine ⟨ht₁.le, fun t => normSqMatrix (U t * (U t₁)ᴴ), fun t ht => ⟨?_, ?_⟩⟩
  · exact normSqMatrix_mem_colStochastic (mul_mem (hU t) (Unitary.star_mem (hU t₁)))
  · rw [recordedAt_Γ_of_le ht, hEφ.envMarginal_of_orthonormal hφ, recordedAt_Γ_at hEφ hunit]

/-- **Approximate decoherence gives approximate division events.** If distinct records
overlap by at most `ε`, the division defect of the recording time is at most
`(N - 1) ε / 2`,
where `N` is the number of configurations. For a perfect record (`ε = 0`) this recovers
`recordedAt_isDivisionEvent`. -/
theorem recordedAt_divisionDefect_le [Nonempty n] {φ : n → m → ℂ} (hEφ : IsRecording φ E e₀)
    (hunit : ∀ j, ∑ e, ‖φ j e‖ ^ 2 = 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ k l, k ≠ l → ‖overlap φ k l‖ ≤ ε) :
    (recordedAt U hU h0 E hE e₀ t₁ ht₁).divisionDefect t₁ ≤ (Fintype.card n - 1) * ε / 2 := by
  have hN : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  refine divisionDefect_le _ (by nlinarith) fun t ht => ?_
  have hW : U t * (U t₁)ᴴ ∈ unitaryGroup n ℂ := mul_mem (hU t) (Unitary.star_mem (hU t₁))
  refine ((recordedAt U hU h0 E hE e₀ t₁ ht₁).factorDefect_le
    (normSqMatrix_mem_colStochastic hW)).trans (colTV_le (by nlinarith) fun j => ?_)
  rw [recordedAt_Γ_at hEφ hunit, recordedAt_Γ_of_le ht]
  set W := U t * (U t₁)ᴴ
  have hcs : ∀ i, (∑ k, ‖W i k‖ * ‖U t₁ k j‖) ^ 2 ≤ 1 := fun i => by
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans (le_of_eq ?_)
    rw [unitary_row_normSq_sum hW, unitary_col_normSq_sum (hU t₁), one_mul]
  have hdiag : ∑ i, ∑ k, (‖W i k‖ * ‖U t₁ k j‖) ^ 2 = 1 := by
    simp_rw [mul_pow]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, unitary_col_normSq_sum hW, one_mul]
    exact unitary_col_normSq_sum (hU t₁) j
  have hsum : ∑ i, |envMarginal (recordedEvolution W E (U t₁)) e₀ i j -
      (normSqMatrix W * normSqMatrix (U t₁)) i j| ≤ (Fintype.card n - 1) * ε := by
    calc _ ≤ ∑ i, ε * ((∑ k, ‖W i k‖ * ‖U t₁ k j‖) ^ 2 - ∑ k, (‖W i k‖ * ‖U t₁ k j‖) ^ 2) :=
          Finset.sum_le_sum fun i _ => hEφ.abs_envMarginal_sub_le hunit hε _ _ i j
      _ = ε * (∑ i, (∑ k, ‖W i k‖ * ‖U t₁ k j‖) ^ 2 - 1) := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, hdiag]
      _ ≤ ε * (Fintype.card n - 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hε0
          have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hcs i
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
          linarith
      _ = (Fintype.card n - 1) * ε := by ring
  linarith

end GenStochasticProcess

end ISM
