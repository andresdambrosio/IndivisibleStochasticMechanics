/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Stochastic.Indivisible

/-!
# Approximate division events

A division event either holds exactly or it does not. Physically, division events are
"often only approximate or effective", valid up to "some given level of precision"
(Barandes, Hasan and Kagan, arXiv:2512.18105, §3.1), but no measure of that precision is
given there. This file proposes one.

The distance between two transition matrices is the worst case, over the initial
configuration `j`, of the total-variation distance between the columns:

  `colTV A B = max_j ½ ∑ᵢ |Aᵢⱼ - Bᵢⱼ|`,

a number in `[0, 1]` for stochastic matrices. The **factorization defect** from `t'` to
`t` is how close a stochastic law `Δ` can bring `Δ Γ(t')` to `Γ(t)`, and the **division
defect** of `t'` is the worst case over later times:

  `δ(t') = sup_{t ≥ t'} inf_{Δ stochastic} colTV (Γ t) (Δ Γ t')`.

## Main results

* `ISM.isCompact_colStochastic`: the stochastic matrices form a compact set, so the
  infimum is attained (`exists_colTV_eq_factorDefect`).
* `ISM.GenStochasticProcess.isDivisionEvent_iff_divisionDefect_eq_zero`: `t' ≥ 0` is a
  division event if and only if its division defect is `0`.

The definitions are original to this project; the choice of the total-variation distance
is one of several reasonable ones (compare the divisibility-based measure of Rivas, Huelga
and Plenio, PRL 105, 050403 (2010)).
-/

@[expose] public section

open Matrix

namespace ISM

variable {n : Type*} [Fintype n]

/-- Worst-case total-variation distance between corresponding columns. -/
noncomputable def colTV (A B : Matrix n n ℝ) : ℝ := ⨆ j, (∑ i, |A i j - B i j|) / 2

theorem colTV_nonneg (A B : Matrix n n ℝ) : 0 ≤ colTV A B :=
  Real.iSup_nonneg fun _ => by positivity

theorem le_colTV (A B : Matrix n n ℝ) (j : n) : (∑ i, |A i j - B i j|) / 2 ≤ colTV A B :=
  le_ciSup (f := fun j => (∑ i, |A i j - B i j|) / 2) (Set.finite_range _).bddAbove j

theorem colTV_le {A B : Matrix n n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j, (∑ i, |A i j - B i j|) / 2 ≤ c) : colTV A B ≤ c :=
  Real.iSup_le h hc

theorem colTV_eq_zero_iff {A B : Matrix n n ℝ} : colTV A B = 0 ↔ A = B := by
  constructor
  · intro h
    ext i j
    have h1 := le_colTV A B j
    rw [h] at h1
    have h2 : ∑ i, |A i j - B i j| = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => abs_nonneg _).1 h2 i
      (Finset.mem_univ _)
    linarith [abs_eq_zero.1 this]
  · rintro rfl
    simp [colTV]

theorem continuous_colTV_mul (G H : Matrix n n ℝ) :
    Continuous fun Δ : Matrix n n ℝ => colTV G (Δ * H) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have : (fun Δ : Matrix n n ℝ => colTV G (Δ * H)) = fun _ => 0 := by
      funext Δ; simp [colTV]
    rw [this]; exact continuous_const
  · simp only [colTV, ← Finset.sup'_univ_eq_ciSup]
    refine Continuous.finset_sup'_apply _ fun j _ => ?_
    simp only [Matrix.mul_apply]
    fun_prop

variable [DecidableEq n]

theorem isCompact_colStochastic : IsCompact (colStochastic ℝ n : Set (Matrix n n ℝ)) := by
  have hsub : (colStochastic ℝ n : Set (Matrix n n ℝ)) ⊆
      Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)) := by
    intro M hM i _ j _
    exact ⟨nonneg_of_mem_colStochastic hM, le_one_of_mem_colStochastic hM⟩
  have hK : IsCompact (Set.pi Set.univ (fun _ : n => Set.pi Set.univ
      (fun _ : n => Set.Icc (0 : ℝ) 1)) : Set (n → n → ℝ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine hK.of_isClosed_subset ?_ hsub
  have : (colStochastic ℝ n : Set (Matrix n n ℝ)) =
      (⋂ i, ⋂ j, {M : Matrix n n ℝ | 0 ≤ M i j}) ∩
        ⋂ j, {M : Matrix n n ℝ | ∑ i, M i j = 1} := by
    ext M
    simp only [SetLike.mem_coe, mem_colStochastic_iff_sum, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_ofPred_eq]
  rw [this]
  refine (isClosed_iInter fun i => isClosed_iInter fun j => ?_).inter
    (isClosed_iInter fun j => ?_)
  · exact isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))
  · exact isClosed_eq (continuous_finsetSum _ fun i _ =>
      (continuous_apply j).comp (continuous_apply i)) continuous_const


theorem colTV_le_one {A B : Matrix n n ℝ} (hA : A ∈ colStochastic ℝ n)
    (hB : B ∈ colStochastic ℝ n) : colTV A B ≤ 1 := by
  refine colTV_le zero_le_one fun j => ?_
  have h : ∑ i, |A i j - B i j| ≤ ∑ i, (A i j + B i j) :=
    Finset.sum_le_sum fun i _ => by
      have := nonneg_of_mem_colStochastic hA (i := i) (j := j)
      have := nonneg_of_mem_colStochastic hB (i := i) (j := j)
      rw [abs_le]; constructor <;> linarith
  rw [Finset.sum_add_distrib, sum_col_of_mem_colStochastic hA,
    sum_col_of_mem_colStochastic hB] at h
  linarith

namespace GenStochasticProcess

variable (P : GenStochasticProcess n)

/-- How far `Γ(t)` is from being obtained from `Γ(t')` by a stochastic law. -/
noncomputable def factorDefect (t' t : ℝ) : ℝ :=
  ⨅ Δ : colStochastic ℝ n, colTV (P.Γ t) ((Δ : Matrix n n ℝ) * P.Γ t')

/-- How far `t'` is from being a division event. -/
noncomputable def divisionDefect (t' : ℝ) : ℝ :=
  ⨆ t : Set.Ici t', P.factorDefect t' t

theorem factorDefect_nonneg (t' t : ℝ) : 0 ≤ P.factorDefect t' t :=
  Real.iInf_nonneg fun _ => colTV_nonneg _ _

theorem factorDefect_le {t' t : ℝ} {Δ : Matrix n n ℝ} (hΔ : Δ ∈ colStochastic ℝ n) :
    P.factorDefect t' t ≤ colTV (P.Γ t) (Δ * P.Γ t') :=
  ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ colTV_nonneg _ _⟩ (⟨Δ, hΔ⟩ : colStochastic ℝ n)

theorem exists_colTV_eq_factorDefect (t' t : ℝ) :
    ∃ Δ ∈ colStochastic ℝ n, colTV (P.Γ t) (Δ * P.Γ t') = P.factorDefect t' t := by
  obtain ⟨Δ, hΔ, hmin⟩ := isCompact_colStochastic.exists_isMinOn
    ⟨1, one_mem _⟩ (continuous_colTV_mul (P.Γ t) (P.Γ t')).continuousOn
  refine ⟨Δ, hΔ, le_antisymm ?_ (P.factorDefect_le hΔ)⟩
  exact le_ciInf fun Δ' => hmin Δ'.2

theorem factorDefect_le_one {t' t : ℝ} (ht' : 0 ≤ t') (ht : t' ≤ t) :
    P.factorDefect t' t ≤ 1 :=
  (P.factorDefect_le (one_mem _)).trans <| by
    rw [one_mul]; exact colTV_le_one (P.stochastic t (ht'.trans ht)) (P.stochastic t' ht')

theorem factorDefect_le_divisionDefect {t' t : ℝ} (ht' : 0 ≤ t') (ht : t' ≤ t) :
    P.factorDefect t' t ≤ P.divisionDefect t' :=
  le_ciSup (f := fun s : Set.Ici t' => P.factorDefect t' s)
    ⟨1, fun _ ⟨s, h⟩ => h ▸ P.factorDefect_le_one ht' s.2⟩ ⟨t, ht⟩

theorem divisionDefect_le {t' c : ℝ} (hc : 0 ≤ c) (h : ∀ t, t' ≤ t → P.factorDefect t' t ≤ c) :
    P.divisionDefect t' ≤ c :=
  Real.iSup_le (fun s => h s s.2) hc

theorem divisionDefect_nonneg (t' : ℝ) : 0 ≤ P.divisionDefect t' :=
  Real.iSup_nonneg fun _ => P.factorDefect_nonneg _ _

theorem isDivisionEvent_iff_divisionDefect_eq_zero {t' : ℝ} (ht' : 0 ≤ t') :
    P.IsDivisionEvent t' ↔ P.divisionDefect t' = 0 := by
  constructor
  · rintro ⟨-, Δ, hΔ⟩
    refine le_antisymm (P.divisionDefect_le le_rfl fun t ht => ?_) (P.divisionDefect_nonneg t')
    refine (P.factorDefect_le (hΔ t ht).1).trans (le_of_eq ?_)
    rw [colTV_eq_zero_iff]; exact (hΔ t ht).2
  · intro h
    have key : ∀ t, t' ≤ t → ∃ Δ, Δ ∈ colStochastic ℝ n ∧ P.Γ t = Δ * P.Γ t' := by
      intro t ht
      obtain ⟨Δ, hΔ, heq⟩ := P.exists_colTV_eq_factorDefect t' t
      have h0 : P.factorDefect t' t = 0 := le_antisymm
        (h ▸ P.factorDefect_le_divisionDefect ht' ht) (P.factorDefect_nonneg t' t)
      exact ⟨Δ, hΔ, colTV_eq_zero_iff.1 (heq.trans h0)⟩
    choose! Δ hΔ using key
    exact ⟨ht', Δ, hΔ⟩

end GenStochasticProcess

end ISM
