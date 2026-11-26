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
* `abs_chsh_stochCorr_le`: the same bound, stated for the transition probabilities of a
  composite process with local unitaries and `±1` outcomes.
* `pointerJoint_eq`, `abs_chsh_pointerCorr_le`: with local ideal apparatuses (chapter 9),
  the pointers' joint distribution is that of "rotate, then read", so the bound holds for
  the pointers too.

The Bell pair reaches `2√2`: see `ISM.BellPair.chsh_bellCorr`.

## References

* J. S. Bell, Physics Physique Fizika 1, 195 (1964).
* J. F. Clauser, M. A. Horne, A. Shimony and R. A. Holt, Phys. Rev. Lett. 23, 880 (1969).
* B. S. Cirel'son, Lett. Math. Phys. 4, 93 (1980).
-/

@[expose] public section

open Matrix Kronecker

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


section Weighted
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A weighted sum of squared amplitudes is an expectation value:
`∑ w(i) |(Wψ)ᵢ|² = ⟨ψ, W† diag(w) W ψ⟩`. -/
theorem sum_mul_norm_sq_mulVec (W : Matrix ι ι ℂ) (w : ι → ℝ) (ψ : ι → ℂ) :
    ∑ i, w i * ‖(W *ᵥ ψ) i‖ ^ 2 =
      expect (Wᴴ * diagonal (fun i => (w i : ℂ)) * W) ψ := by
  rw [expect, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  simp only [dotProduct, mulVec_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply]
  set y := (W *ᵥ ψ) i
  rw [show star y * ((w i : ℂ) * y) = (w i : ℂ) * (y * star y) by ring, Complex.star_def,
    Complex.mul_conj']
  norm_cast

end Weighted

section Stochastic
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **Correlations from transition probabilities.** After the preparation `Θ` (from
configuration `j`), Alice applies `U x` and Bob `V y`, and both configurations are read with
outcomes `a x` and `b y`. `E(x, y) = ∑ a(i₁) b(i₂) Γ((i₁, i₂), j)`, where `Γ` is the
transition matrix of the composite process. -/
noncomputable def stochCorr (Θ : Matrix (A × B) (A × B) ℂ) (U : Fin 2 → Matrix A A ℂ)
    (V : Fin 2 → Matrix B B ℂ) (a : Fin 2 → A → ℝ) (b : Fin 2 → B → ℝ) (j : A × B)
    (x y : Fin 2) : ℝ :=
  ∑ i : A × B, a x i.1 * b y i.2 * normSqMatrix ((U x ⊗ₖ V y) * Θ) i j

/-- The observable measured by "rotate by `U`, then read the configuration with outcome
`a`": `Uᴴ diag(a) U`. -/
noncomputable def rotObs {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (a : n → ℝ) : Matrix n n ℂ :=
  Uᴴ * diagonal (fun i => (a i : ℂ)) * U

/-- The stochastic correlation is the quantum expectation of `(Uᴴ D_a U) ⊗ (Vᴴ D_b V)` in
the state `Θ eⱼ`. -/
theorem stochCorr_eq_expect (Θ : Matrix (A × B) (A × B) ℂ) (U : Fin 2 → Matrix A A ℂ)
    (V : Fin 2 → Matrix B B ℂ) (a : Fin 2 → A → ℝ) (b : Fin 2 → B → ℝ) (j : A × B)
    (x y : Fin 2) :
    stochCorr Θ U V a b j x y =
      expect ((rotObs (U x) (a x) ⊗ₖ (1 : Matrix B B ℂ)) *
        ((1 : Matrix A A ℂ) ⊗ₖ rotObs (V y) (b y))) (fun k => Θ k j) := by
  have hcol : ∀ i, ((U x ⊗ₖ V y) * Θ) i j = ((U x ⊗ₖ V y) *ᵥ fun k => Θ k j) i := by
    intro i; simp [Matrix.mul_apply, mulVec, dotProduct]
  have := sum_mul_norm_sq_mulVec (U x ⊗ₖ V y) (fun i => a x i.1 * b y i.2)
    (fun k => Θ k j)
  simp only [stochCorr, normSqMatrix, of_apply, hcol]
  rw [this, ← mul_kronecker_mul, mul_one, one_mul, rotObs, rotObs]
  congr 1
  rw [conjTranspose_kronecker, show (diagonal fun i : A × B => ((a x i.1 * b y i.2 : ℝ) : ℂ)) =
      diagonal (fun i => (a x i : ℂ)) ⊗ₖ diagonal (fun i => (b y i : ℂ)) by
    rw [diagonal_kronecker_diagonal]; congr 1; ext i; push_cast; rfl,
    ← mul_kronecker_mul, ← mul_kronecker_mul]

omit [DecidableEq A] [DecidableEq B] in
/-- Flipping Alice's outcomes flips the correlations. -/
theorem stochCorr_neg (Θ : Matrix (A × B) (A × B) ℂ) (U : Fin 2 → Matrix A A ℂ)
    (V : Fin 2 → Matrix B B ℂ) (a : Fin 2 → A → ℝ) (b : Fin 2 → B → ℝ) (j : A × B) :
    stochCorr Θ U V (fun x i => -a x i) b j = fun x y => -stochCorr Θ U V a b j x y := by
  ext x y; simp [stochCorr, neg_mul, Finset.sum_neg_distrib]

section Obs
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Uᴴ diag(a) U` is Hermitian for real `a`. -/
theorem rotObs_isHermitian (U : Matrix n n ℂ) (a : n → ℝ) : (rotObs U a).IsHermitian := by
  simp [IsHermitian, rotObs, conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc]
  congr 3
  ext i
  simp

/-- For a unitary `U` and outcomes `±1`, `(Uᴴ diag(a) U)² = 1`. -/
theorem rotObs_mul_self {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) {a : n → ℝ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) : rotObs U a * rotObs U a = 1 := by
  have h1 : U * Uᴴ = 1 := mem_unitaryGroup_iff.mp hU
  have h2 : Uᴴ * U = 1 := mem_unitaryGroup_iff'.mp hU
  have hd : diagonal (fun i => (a i : ℂ)) * diagonal (fun i => (a i : ℂ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i
    rcases ha i with h | h <;> simp [h]
  calc rotObs U a * rotObs U a
      = Uᴴ * (diagonal (fun i => (a i : ℂ)) * (U * Uᴴ) * diagonal (fun i => (a i : ℂ))) * U := by
        simp only [rotObs, Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, hd, Matrix.mul_one, h2]

end Obs

/-- **Tsirelson's bound for transition probabilities** (Cirel'son 1980, restated): for any
unitary preparation `Θ`, any local unitaries and any `±1` outcomes, the CHSH value of the
composite process's transition probabilities is at most `2√2`. -/
theorem abs_chsh_stochCorr_le {Θ : Matrix (A × B) (A × B) ℂ} (hΘ : Θ ∈ unitaryGroup (A × B) ℂ)
    {U : Fin 2 → Matrix A A ℂ} (hU : ∀ x, U x ∈ unitaryGroup A ℂ)
    {V : Fin 2 → Matrix B B ℂ} (hV : ∀ y, V y ∈ unitaryGroup B ℂ)
    {a : Fin 2 → A → ℝ} (ha : ∀ x i, a x i = 1 ∨ a x i = -1)
    {b : Fin 2 → B → ℝ} (hb : ∀ y i, b y i = 1 ∨ b y i = -1) (j : A × B) :
    |chsh (stochCorr Θ U V a b j)| ≤ 2 * Real.sqrt 2 := by
  have hψ : ∑ k, ‖Θ k j‖ ^ 2 = 1 := unitary_col_normSq_sum hΘ j
  -- the upper bound, for any sign functions on Alice's side
  have key : ∀ a' : Fin 2 → A → ℝ, (∀ x i, a' x i = 1 ∨ a' x i = -1) →
      chsh (stochCorr Θ U V a' b j) ≤ 2 * Real.sqrt 2 := by
    intro a' ha'
    set Ah : Fin 2 → Matrix (A × B) (A × B) ℂ := fun x => rotObs (U x) (a' x) ⊗ₖ 1
    set Bh : Fin 2 → Matrix (A × B) (A × B) ℂ := fun y => 1 ⊗ₖ rotObs (V y) (b y)
    have hA : ∀ x, (Ah x).IsHermitian := fun x => by
      simp only [Ah, IsHermitian, conjTranspose_kronecker, conjTranspose_one,
        (rotObs_isHermitian _ _).eq]
    have hB : ∀ y, (Bh y).IsHermitian := fun y => by
      simp only [Bh, IsHermitian, conjTranspose_kronecker, conjTranspose_one,
        (rotObs_isHermitian _ _).eq]
    have hA2 : ∀ x, Ah x * Ah x = 1 := fun x => by
      simp only [Ah, ← mul_kronecker_mul, rotObs_mul_self (hU x) (ha' x), Matrix.mul_one,
        one_kronecker_one]
    have hB2 : ∀ y, Bh y * Bh y = 1 := fun y => by
      simp only [Bh, ← mul_kronecker_mul, rotObs_mul_self (hV y) (hb y), Matrix.mul_one,
        one_kronecker_one]
    have hc : ∀ x y, Ah x * Bh y = Bh y * Ah x := fun x y => by
      simp only [Ah, Bh, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
    have h := expect_chsh_le (hA 0) (hA 1) (hB 0) (hB 1) (hA2 0) (hA2 1) (hB2 0) (hB2 1)
      (hc 0 0) (hc 0 1) (hc 1 0) (hc 1 1) (fun k => Θ k j)
    rw [hψ, mul_one, expect_sub, expect_add, expect_add] at h
    simpa only [chsh, stochCorr_eq_expect] using h
  have h1 := key a ha
  have h2 := key (fun x i => -a x i) fun x i => (ha x i).symm.imp (by intro h; simp [h])
    (by intro h; simp [h])
  rw [stochCorr_neg] at h2
  simp only [chsh] at h1 h2 ⊢
  rw [abs_le]; constructor <;> linarith

end Stochastic

section Apparatus
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Alice's apparatus `M` and Bob's apparatus `N` acting together on the two systems and
their two pointers. Each acts only on its own system and pointer. -/
def localPair (M : Matrix (A × Option A) (A × Option A) ℂ)
    (N : Matrix (B × Option B) (B × Option B) ℂ) :
    Matrix ((A × B) × (Option A × Option B)) ((A × B) × (Option A × Option B)) ℂ :=
  of fun r c => M (r.1.1, r.2.1) (c.1.1, c.2.1) * N (r.1.2, r.2.2) (c.1.2, c.2.2)

/-- The joint distribution of the two pointers: the probability that Alice's pointer
reads `a` and Bob's reads `b`, starting from configuration `j` with both pointers ready,
after the preparation `Θ` and then both measurements. -/
noncomputable def pointerJoint (M : Matrix (A × Option A) (A × Option A) ℂ)
    (N : Matrix (B × Option B) (B × Option B) ℂ) (Θ : Matrix (A × B) (A × B) ℂ) (j : A × B)
    (a : A) (b : B) : ℝ :=
  ∑ i : A × B, ‖(localPair M N * (Θ ⊗ₖ (1 : Matrix (Option A × Option B)
    (Option A × Option B) ℂ))) (i, (some a, some b)) (j, (none, none))‖ ^ 2

/-- The amplitude after two local ideal measurements. -/
theorem localPair_apply_amp {V : Matrix A A ℂ} {W : Matrix B B ℂ}
    {M : Matrix (A × Option A) (A × Option A) ℂ} {N : Matrix (B × Option B) (B × Option B) ℂ}
    (hM : IsIdealMeasurement V M) (hN : IsIdealMeasurement W N)
    (Θ : Matrix (A × B) (A × B) ℂ) (j : A × B) (i : A × B) (a : A) (b : B) :
    (localPair M N * (Θ ⊗ₖ (1 : Matrix (Option A × Option B) (Option A × Option B) ℂ)))
      (i, (some a, some b)) (j, (none, none)) =
      V i.1 a * W i.2 b * ((Vᴴ ⊗ₖ Wᴴ) * Θ) (a, b) j := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single ((none, none) : Option A × Option B)]
  · simp only [localPair, of_apply, kroneckerMap_apply, one_apply_eq, mul_one,
      (hM.2 _ _).2, (hN.2 _ _).2, conjTranspose_apply]
    ring
  · intro x _ hx
    simp [one_apply_ne hx]
  · simp

/-- **Measuring with local apparatuses is rotating and reading.** With ideal measurements in
the bases `V` and `W` (chapter 9), the pointers read `(a, b)` with probability
`|((Vᴴ ⊗ Wᴴ) Θ)_{(a,b), j}|²`. -/
theorem pointerJoint_eq {V : Matrix A A ℂ} {W : Matrix B B ℂ}
    {M : Matrix (A × Option A) (A × Option A) ℂ} {N : Matrix (B × Option B) (B × Option B) ℂ}
    (hM : IsIdealMeasurement V M) (hN : IsIdealMeasurement W N)
    (hV : V ∈ unitaryGroup A ℂ) (hW : W ∈ unitaryGroup B ℂ)
    (Θ : Matrix (A × B) (A × B) ℂ) (j : A × B) (a : A) (b : B) :
    pointerJoint M N Θ j a b = normSqMatrix ((Vᴴ ⊗ₖ Wᴴ) * Θ) (a, b) j := by
  simp only [pointerJoint, localPair_apply_amp hM hN, norm_mul, mul_pow,
    Fintype.sum_prod_type, normSqMatrix, of_apply]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, unitary_col_normSq_sum hW b, mul_one,
    unitary_col_normSq_sum hV a, one_mul]

/-- The correlations of the two pointers' readings, with outcomes `a x` and `b y`. -/
noncomputable def pointerCorr (M : Fin 2 → Matrix (A × Option A) (A × Option A) ℂ)
    (N : Fin 2 → Matrix (B × Option B) (B × Option B) ℂ) (Θ : Matrix (A × B) (A × B) ℂ)
    (a : Fin 2 → A → ℝ) (b : Fin 2 → B → ℝ) (j : A × B) (x y : Fin 2) : ℝ :=
  ∑ p : A × B, a x p.1 * b y p.2 * pointerJoint (M x) (N y) Θ j p.1 p.2

/-- Pointer correlations are the stochastic correlations with `U = Vᴴ`, `V = Wᴴ`. -/
theorem pointerCorr_eq {V : Fin 2 → Matrix A A ℂ} {W : Fin 2 → Matrix B B ℂ}
    {M : Fin 2 → Matrix (A × Option A) (A × Option A) ℂ}
    {N : Fin 2 → Matrix (B × Option B) (B × Option B) ℂ}
    (hM : ∀ x, IsIdealMeasurement (V x) (M x)) (hN : ∀ y, IsIdealMeasurement (W y) (N y))
    (hV : ∀ x, V x ∈ unitaryGroup A ℂ) (hW : ∀ y, W y ∈ unitaryGroup B ℂ)
    (Θ : Matrix (A × B) (A × B) ℂ) (a : Fin 2 → A → ℝ) (b : Fin 2 → B → ℝ) (j : A × B) :
    pointerCorr M N Θ a b j = stochCorr Θ (fun x => (V x)ᴴ) (fun y => (W y)ᴴ) a b j := by
  ext x y
  simp only [pointerCorr, stochCorr, pointerJoint_eq (hM x) (hN y) (hV x) (hW y)]

/-- **Tsirelson's bound for local apparatuses:** whatever ideal measurements Alice and Bob
make, after any unitary preparation, the pointers' CHSH value is at most `2√2`. -/
theorem abs_chsh_pointerCorr_le {Θ : Matrix (A × B) (A × B) ℂ}
    (hΘ : Θ ∈ unitaryGroup (A × B) ℂ) {V : Fin 2 → Matrix A A ℂ} {W : Fin 2 → Matrix B B ℂ}
    {M : Fin 2 → Matrix (A × Option A) (A × Option A) ℂ}
    {N : Fin 2 → Matrix (B × Option B) (B × Option B) ℂ}
    (hM : ∀ x, IsIdealMeasurement (V x) (M x)) (hN : ∀ y, IsIdealMeasurement (W y) (N y))
    (hV : ∀ x, V x ∈ unitaryGroup A ℂ) (hW : ∀ y, W y ∈ unitaryGroup B ℂ)
    {a : Fin 2 → A → ℝ} (ha : ∀ x i, a x i = 1 ∨ a x i = -1)
    {b : Fin 2 → B → ℝ} (hb : ∀ y i, b y i = 1 ∨ b y i = -1) (j : A × B) :
    |chsh (pointerCorr M N Θ a b j)| ≤ 2 * Real.sqrt 2 := by
  rw [pointerCorr_eq hM hN hV hW]
  exact abs_chsh_stochCorr_le hΘ (fun x => Unitary.star_mem (hV x))
    (fun y => Unitary.star_mem (hW y)) ha hb j

end Apparatus

end ISM
