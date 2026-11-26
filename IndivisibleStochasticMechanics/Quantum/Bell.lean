/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Quantum.Composite

/-!
# Bell nonlocality: the CHSH inequality and Tsirelson's bound

* `LHVModel.abs_chsh_corr_le_two`: every local hidden-variable model satisfies the CHSH
  inequality `|S| ≤ 2` (Clauser, Horne, Shimony and Holt 1969, after Bell 1964).
* `expect_chsh_le`: quantum mechanics satisfies Tsirelson's bound `S ≤ 2√2`
  (Cirel'son 1980), by the standard sum-of-squares argument.

The Bell pair reaches `2√2`: see `ISM.BellPair.chsh_bellCorr`.

## References

* J. S. Bell, Physics Physique Fizika 1, 195 (1964).
* J. F. Clauser, M. A. Horne, A. Shimony and R. A. Holt, Phys. Rev. Lett. 23, 880 (1969).
* B. S. Cirel'son, Lett. Math. Phys. 4, 93 (1980).
-/

@[expose] public section

open Matrix

namespace ISM


/-- The CHSH combination `E₀₀ + E₀₁ + E₁₀ - E₁₁` of four correlations. -/
def chsh (E : Fin 2 → Fin 2 → ℝ) : ℝ := E 0 0 + E 0 1 + E 1 0 - E 1 1

/-- A **local hidden-variable model** for a two-party, two-setting experiment, in the sense of
Bell (1964) and Clauser–Horne–Shimony–Holt (1969). A hidden variable `l` is drawn from `μ`;
Alice's outcome for setting `x` is `α x l` and Bob's for setting `y` is `β y l`, both in
`[-1, 1]`. Locality: Alice's outcome does not depend on `y`, nor Bob's on `x`. Outcomes in
`[-1, 1]` (rather than `±1`) also cover local randomness, as averages. -/
structure LHVModel (Λ : Type*) [Fintype Λ] where
  μ : Λ → ℝ
  isProbDist : IsProbDist μ
  α : Fin 2 → Λ → ℝ
  β : Fin 2 → Λ → ℝ
  abs_α_le : ∀ x l, |α x l| ≤ 1
  abs_β_le : ∀ y l, |β y l| ≤ 1

namespace LHVModel
variable {Λ : Type*} [Fintype Λ] (L : LHVModel Λ)

/-- The correlation `E(x, y) = ∑ μ(l) α(x, l) β(y, l)`. -/
def corr (x y : Fin 2) : ℝ := ∑ l, L.μ l * (L.α x l * L.β y l)

/-- The pointwise bound `|a₀b₀ + a₀b₁ + a₁b₀ - a₁b₁| ≤ 2` for numbers in `[-1, 1]`. -/
theorem abs_bracket_le (a₀ a₁ b₀ b₁ : ℝ) (ha₀ : |a₀| ≤ 1) (ha₁ : |a₁| ≤ 1)
    (hb₀ : |b₀| ≤ 1) (hb₁ : |b₁| ≤ 1) :
    |a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁| ≤ 2 := by
  have h1 : |a₀ * (b₀ + b₁)| ≤ |b₀ + b₁| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ha₀
  have h2 : |a₁ * (b₀ - b₁)| ≤ |b₀ - b₁| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ha₁
  have h3 : |b₀ + b₁| + |b₀ - b₁| ≤ 2 := by
    rw [abs_le] at hb₀ hb₁
    rcases abs_cases (b₀ + b₁) with ⟨e, _⟩ | ⟨e, _⟩ <;>
      rcases abs_cases (b₀ - b₁) with ⟨f, _⟩ | ⟨f, _⟩ <;> rw [e, f] <;> linarith
  calc |a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁|
      = |a₀ * (b₀ + b₁) + a₁ * (b₀ - b₁)| := by ring_nf
    _ ≤ |a₀ * (b₀ + b₁)| + |a₁ * (b₀ - b₁)| := abs_add_le _ _
    _ ≤ 2 := by linarith

/-- **The CHSH inequality** (Clauser, Horne, Shimony and Holt, 1969): every local
hidden-variable model satisfies `|E₀₀ + E₀₁ + E₁₀ - E₁₁| ≤ 2`. -/
theorem abs_chsh_corr_le_two : |chsh L.corr| ≤ 2 := by
  have h : chsh L.corr = ∑ l, L.μ l *
      (L.α 0 l * L.β 0 l + L.α 0 l * L.β 1 l + L.α 1 l * L.β 0 l - L.α 1 l * L.β 1 l) := by
    simp only [chsh, corr, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h]
  calc |∑ l, L.μ l * _| ≤ ∑ l, |L.μ l * _| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, L.μ l * 2 := Finset.sum_le_sum fun l _ => by
        rw [abs_mul, abs_of_nonneg (L.isProbDist.nonneg l)]
        exact mul_le_mul_of_nonneg_left (abs_bracket_le _ _ _ _ (L.abs_α_le 0 l)
          (L.abs_α_le 1 l) (L.abs_β_le 0 l) (L.abs_β_le 1 l)) (L.isProbDist.nonneg l)
    _ = 2 := by rw [← Finset.sum_mul, L.isProbDist.sum_eq_one, one_mul]

end LHVModel

section Tsirelson

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum-of-squares identity behind Tsirelson's bound: with `s² = 2`,
`(sA₀ - B₀ - B₁)² + (sA₁ - B₀ + B₁)² = 8 - 2s·C`, where `C` is the CHSH operator. -/
theorem sos_identity {A₀ A₁ B₀ B₁ : Matrix ι ι ℂ} (s : ℂ) (hs : s * s = 2)
    (hA₀ : A₀ * A₀ = 1) (hA₁ : A₁ * A₁ = 1) (hB₀ : B₀ * B₀ = 1) (hB₁ : B₁ * B₁ = 1)
    (h₀₀ : A₀ * B₀ = B₀ * A₀) (h₀₁ : A₀ * B₁ = B₁ * A₀)
    (h₁₀ : A₁ * B₀ = B₀ * A₁) (h₁₁ : A₁ * B₁ = B₁ * A₁) :
    (s • A₀ - (B₀ + B₁)) * (s • A₀ - (B₀ + B₁)) + (s • A₁ - (B₀ - B₁)) * (s • A₁ - (B₀ - B₁)) =
      (8 : ℂ) • (1 : Matrix ι ι ℂ) - (2 * s) • (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) := by
  simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    hA₀, hA₁, hB₀, hB₁, ← h₀₀, ← h₀₁, ← h₁₀, ← h₁₁]
  match_scalars <;> first | ring1 | linear_combination (2 : ℂ) * hs

/-- The expectation value `Re ⟨ψ, X ψ⟩`. -/
noncomputable def expect (X : Matrix ι ι ℂ) (ψ : ι → ℂ) : ℝ := (star ψ ⬝ᵥ X *ᵥ ψ).re

omit [DecidableEq ι] in
/-- `⟨ψ, X†X ψ⟩ = ‖Xψ‖² ≥ 0`. -/
theorem expect_conjTranspose_mul_self (X : Matrix ι ι ℂ) (ψ : ι → ℂ) :
    expect (Xᴴ * X) ψ = ∑ i, ‖(X *ᵥ ψ) i‖ ^ 2 := by
  rw [expect, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  simp [dotProduct, Complex.mul_conj', mul_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

omit [DecidableEq ι] in
/-- Expectation is additive. -/
theorem expect_add (X Y : Matrix ι ι ℂ) (ψ : ι → ℂ) :
    expect (X + Y) ψ = expect X ψ + expect Y ψ := by
  simp [expect, add_mulVec, dotProduct_add]

omit [DecidableEq ι] in
/-- Expectation respects subtraction. -/
theorem expect_sub (X Y : Matrix ι ι ℂ) (ψ : ι → ℂ) :
    expect (X - Y) ψ = expect X ψ - expect Y ψ := by
  simp [expect, sub_mulVec, dotProduct_sub]

omit [DecidableEq ι] in
/-- Expectation is real-homogeneous. -/
theorem expect_real_smul (r : ℝ) (X : Matrix ι ι ℂ) (ψ : ι → ℂ) :
    expect ((r : ℂ) • X) ψ = r * expect X ψ := by
  simp [expect, Matrix.smul_mulVec, dotProduct_smul]

/-- The expectation of `1` is `‖ψ‖²`. -/
theorem expect_one (ψ : ι → ℂ) : expect 1 ψ = ∑ i, ‖ψ i‖ ^ 2 := by
  simpa using expect_conjTranspose_mul_self (1 : Matrix ι ι ℂ) ψ

/-- **Tsirelson's bound** (Cirel'son, 1980): for `±1`-valued observables (Hermitian, squaring
to `1`) where Alice's commute with Bob's, the CHSH operator has expectation at most
`2√2 ‖ψ‖²`. Commuting operators on one space cover the tensor-product case `A ⊗ 1`, `1 ⊗ B`.
The proof is the standard sum-of-squares argument. -/
theorem expect_chsh_le {A₀ A₁ B₀ B₁ : Matrix ι ι ℂ}
    (hA₀ : A₀.IsHermitian) (hA₁ : A₁.IsHermitian) (hB₀ : B₀.IsHermitian)
    (hB₁ : B₁.IsHermitian)
    (hA₀₂ : A₀ * A₀ = 1) (hA₁₂ : A₁ * A₁ = 1) (hB₀₂ : B₀ * B₀ = 1) (hB₁₂ : B₁ * B₁ = 1)
    (h₀₀ : A₀ * B₀ = B₀ * A₀) (h₀₁ : A₀ * B₁ = B₁ * A₀)
    (h₁₀ : A₁ * B₀ = B₀ * A₁) (h₁₁ : A₁ * B₁ = B₁ * A₁) (ψ : ι → ℂ) :
    expect (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) ψ ≤
      2 * Real.sqrt 2 * ∑ i, ‖ψ i‖ ^ 2 := by
  set s : ℝ := Real.sqrt 2 with hs_def
  have hs : (s : ℂ) * s = 2 := by exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  set X := (s : ℂ) • A₀ - (B₀ + B₁)
  set Y := (s : ℂ) • A₁ - (B₀ - B₁)
  have hX : Xᴴ = X := by
    simp [X, conjTranspose_sub, conjTranspose_add, conjTranspose_smul, hA₀.eq, hB₀.eq, hB₁.eq]
  have hY : Yᴴ = Y := by
    simp [Y, conjTranspose_sub, conjTranspose_smul, hA₁.eq, hB₀.eq, hB₁.eq]
  have key : X * X + Y * Y = (8 : ℂ) • (1 : Matrix ι ι ℂ) -
      (2 * (s : ℂ)) • (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) :=
    sos_identity (s : ℂ) hs hA₀₂ hA₁₂ hB₀₂ hB₁₂ h₀₀ h₀₁ h₁₀ h₁₁
  have e : expect (X * X + Y * Y) ψ = expect ((8 : ℂ) • (1 : Matrix ι ι ℂ) -
      (2 * (s : ℂ)) • (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)) ψ := by rw [key]
  have hXX : expect (X * X) ψ = ∑ i, ‖(X *ᵥ ψ) i‖ ^ 2 := by
    have := expect_conjTranspose_mul_self X ψ; rwa [hX] at this
  have hYY : expect (Y * Y) ψ = ∑ i, ‖(Y *ᵥ ψ) i‖ ^ 2 := by
    have := expect_conjTranspose_mul_self Y ψ; rwa [hY] at this
  rw [expect_add, hXX, hYY, expect_sub,
    show ((8 : ℂ)) = ((8 : ℝ) : ℂ) by norm_num, expect_real_smul,
    show (2 * (s : ℂ)) = ((2 * s : ℝ) : ℂ) by push_cast; ring, expect_real_smul,
    expect_one] at e
  have h1 : 0 ≤ ∑ i, ‖(X *ᵥ ψ) i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have h2 : 0 ≤ ∑ i, ‖(Y *ᵥ ψ) i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have h3 : s * s = 2 := Real.mul_self_sqrt (by norm_num)
  have h4 : s * expect (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) ψ ≤
      s * (2 * s * ∑ i, ‖ψ i‖ ^ 2) := by
    have : s * (2 * s * ∑ i, ‖ψ i‖ ^ 2) = 4 * ∑ i, ‖ψ i‖ ^ 2 := by
      rw [show s * (2 * s * ∑ i, ‖ψ i‖ ^ 2) = 2 * (s * s) * ∑ i, ‖ψ i‖ ^ 2 by ring, h3]; ring
    rw [this]; linarith
  exact le_of_mul_le_mul_left h4 hspos

end Tsirelson

end ISM
