/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Quantum.Measurement

/-!
# Collapse as a division event

Textbook quantum mechanics adds a second dynamical law to unitary evolution: after a
measurement with outcome `a`, the state *collapses* to the eigenvector `v a`. In
Indivisible Stochastic Mechanics there is no second law. A measurement is an ordinary
interaction with an apparatus, and the composite system keeps evolving unitarily.

We show that collapse is a *consequence*. The system starts in configuration `j` with the
pointer ready. It evolves by `U`, is measured by an ideal measurement `M` of the observable
with eigenvectors `v a` (the columns of `V`), and then evolves by `W`. Then

  `Θ((i, a) ← (j, ready)) = (W v_a)ᵢ · ⟨v_a| U |j⟩`,

so the joint probability of "system in `i`, pointer at `a`" is

  `P(i, a | j) = |(W v_a)ᵢ|² · |⟨v_a| U |j⟩|²`.

This is exactly the textbook recipe: outcome `a` with Born probability, *then* evolution
from the collapsed state `v_a`. The later statistics depend on the past only through the
recorded outcome `a`. Summing over the pointer kills the interference terms:

  `Γ_sys = |W V|² · |Vᴴ U|²`   instead of   `|W U|² = |(W V)(Vᴴ U)|²`.

When the measured observable is the configuration itself (`V = 1`), the measurement time
becomes a **division event** of the system's process, for *any* unitary dynamics. This is
Barandes' account of collapse: measurement does not change the laws, it creates a division
event.

## Main definitions

* `ISM.measuredEvolution W M U`: evolve by `U`, measure with `M`, evolve by `W`.
* `ISM.pointerMarginal Θ`: the system's transition matrix, summing over the pointer, with the
  pointer initially ready.
* `ISM.GenStochasticProcess.measuredAt`: the system's process when it evolves by `U t` and its
  configuration is measured at time `t₁`.

## Main results

* `ISM.IsIdealMeasurement.collapse_apply`: the collapse amplitude formula above.
* `ISM.IsIdealMeasurement.pointerMarginal_measuredEvolution`: `Γ_sys = |W V|² · |Vᴴ U|²`.
* `ISM.GenStochasticProcess.measuredAt_isDivisionEvent`: measuring the configuration at
  `t₁` makes `t₁` a division event.

## References

* J. A. Barandes, *The Stochastic-Quantum Correspondence*, arXiv:2302.10778
  (measurement, collapse and division events).
* J. von Neumann, *Mathematical Foundations of Quantum Mechanics* (1932), ch. VI.
-/

@[expose] public section

open Matrix Kronecker

namespace ISM

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- After evolving by `U` and measuring, the amplitude for pointer `a` is
`V k a · ⟨v_a| U |j⟩`. -/
theorem IsIdealMeasurement.mul_apply_some {V U : Matrix n n ℂ}
    {M : Matrix (n × Option n) (n × Option n) ℂ} (hM : IsIdealMeasurement V M) (k j a : n) :
    (M * (U ⊗ₖ (1 : Matrix (Option n) (Option n) ℂ))) (k, some a) (j, none) =
      V k a * (Vᴴ * U) a j := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_option, kroneckerMap_apply,
    Matrix.one_apply]
  simp [(hM.2 _ _).2, Finset.mul_sum, conjTranspose_apply, mul_assoc]

/-- After an ideal measurement the pointer is never left ready. -/
theorem IsIdealMeasurement.mul_apply_none {V U : Matrix n n ℂ}
    {M : Matrix (n × Option n) (n × Option n) ℂ} (hM : IsIdealMeasurement V M) (k j : n) :
    (M * (U ⊗ₖ (1 : Matrix (Option n) (Option n) ℂ))) (k, none) (j, none) = 0 := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_option, kroneckerMap_apply,
    Matrix.one_apply]
  simp [(hM.2 _ _).1]

omit [DecidableEq n] in
/-- An evolution `W ⊗ 1` that does not touch the pointer only mixes system configurations. -/
theorem kron_one_mul_apply {m : Type*} [Fintype m] [DecidableEq m] (W : Matrix n n ℂ)
    (X : Matrix (n × m) (n × m) ℂ) (i : n) (p : m) (c : n × m) :
    ((W ⊗ₖ (1 : Matrix m m ℂ)) * X) (i, p) c = ∑ k, W i k * X (k, p) c := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]

/-- Evolve the system by `U`, measure with `M`, then evolve the system by `W`. The pointer is
left untouched by `U` and `W`. -/
def measuredEvolution (W : Matrix n n ℂ) (M : Matrix (n × Option n) (n × Option n) ℂ)
    (U : Matrix n n ℂ) : Matrix (n × Option n) (n × Option n) ℂ :=
  (W ⊗ₖ (1 : Matrix (Option n) (Option n) ℂ)) *
    (M * (U ⊗ₖ (1 : Matrix (Option n) (Option n) ℂ)))

/-- **Collapse.** Evolve by `U`, measure, then evolve by `W`. The amplitude for "system in
`i`, pointer at `a`" is `(W v_a)ᵢ · ⟨v_a| U |j⟩`: the Born amplitude for `a`, times the
amplitude of evolving from the collapsed state `v_a`. -/
theorem IsIdealMeasurement.collapse_apply {V U W : Matrix n n ℂ}
    {M : Matrix (n × Option n) (n × Option n) ℂ} (hM : IsIdealMeasurement V M) (i j a : n) :
    measuredEvolution W M U (i, some a) (j, none) =
      (W * V) i a * (Vᴴ * U) a j := by
  rw [measuredEvolution, kron_one_mul_apply]
  simp_rw [hM.mul_apply_some, Matrix.mul_apply, Finset.sum_mul, mul_assoc]

/-- After the measurement the pointer is never found ready. -/
theorem IsIdealMeasurement.collapse_apply_none {V U W : Matrix n n ℂ}
    {M : Matrix (n × Option n) (n × Option n) ℂ} (hM : IsIdealMeasurement V M) (i j : n) :
    measuredEvolution W M U (i, none) (j, none) = 0 := by
  rw [measuredEvolution, kron_one_mul_apply]
  simp [hM.mul_apply_none]

/-- The matrix of squared moduli `|A|²`, entrywise. -/
noncomputable def normSqMatrix (A : Matrix n n ℂ) : Matrix n n ℝ :=
  Matrix.of fun i j => ‖A i j‖ ^ 2

/-- Summing over the pointer: the interference terms between outcomes drop out. -/
theorem IsIdealMeasurement.marginal {V U W : Matrix n n ℂ}
    {M : Matrix (n × Option n) (n × Option n) ℂ} (hM : IsIdealMeasurement V M) (i j : n) :
    ∑ p, ‖measuredEvolution W M U (i, p) (j, none)‖ ^ 2
      = (normSqMatrix (W * V) * normSqMatrix (Vᴴ * U)) i j := by
  simp [Fintype.sum_option, hM.collapse_apply, hM.collapse_apply_none, Matrix.mul_apply,
    normSqMatrix, mul_pow]

omit [Fintype n] in
theorem normSqMatrix_one : normSqMatrix (1 : Matrix n n ℂ) = 1 := by
  ext i j; by_cases h : i = j <;> simp [normSqMatrix, Matrix.one_apply, h]

/-- `|A|²` is stochastic when `A` is unitary. -/
theorem normSqMatrix_mem_colStochastic {A : Matrix n n ℂ} (hA : A ∈ unitaryGroup n ℂ) :
    normSqMatrix A ∈ colStochastic ℝ n :=
  (isUnistochastic_normSq hA).mem_colStochastic

/-- The system's transition matrix from a composite evolution `Θ`, summing over the final
pointer configuration, with the pointer initially ready. -/
noncomputable def pointerMarginal (Θ : Matrix (n × Option n) (n × Option n) ℂ) :
    Matrix n n ℝ :=
  Matrix.of fun i j => ∑ p, ‖Θ (i, p) (j, none)‖ ^ 2

/-- Without a measurement, the system marginal of `A ⊗ 1` is just `|A|²`. -/
theorem pointerMarginal_kron_one (A : Matrix n n ℂ) :
    pointerMarginal (A ⊗ₖ (1 : Matrix (Option n) (Option n) ℂ)) = normSqMatrix A := by
  ext i j; simp [pointerMarginal, normSqMatrix, Fintype.sum_option]

/-- **Measurement removes interference.** The system's transition matrix after
evolve–measure–evolve is `|W V|² · |Vᴴ U|²`: a product of two stochastic matrices, with the
outcome `a` as the intermediate configuration. -/
theorem IsIdealMeasurement.pointerMarginal_measuredEvolution {V U W : Matrix n n ℂ}
    {M : Matrix (n × Option n) (n × Option n) ℂ} (hM : IsIdealMeasurement V M) :
    pointerMarginal (measuredEvolution W M U) = normSqMatrix (W * V) * normSqMatrix (Vᴴ * U) := by
  ext i j; exact hM.marginal i j

/-- Composite evolution when the system evolves by `U t` and its configuration is measured
at `t₁`: `U t ⊗ 1` before `t₁`, and `(U t U(t₁)† ⊗ 1) M (U t₁ ⊗ 1)` from `t₁` on.
-/
noncomputable def measuredComposite (U : ℝ → Matrix n n ℂ)
    (M : Matrix (n × Option n) (n × Option n) ℂ) (t₁ t : ℝ) :
    Matrix (n × Option n) (n × Option n) ℂ :=
  if t < t₁ then U t ⊗ₖ (1 : Matrix (Option n) (Option n) ℂ)
  else measuredEvolution (U t * (U t₁)ᴴ) M (U t₁)

theorem measuredComposite_mem_unitaryGroup {U : ℝ → Matrix n n ℂ}
    (hU : ∀ t, U t ∈ unitaryGroup n ℂ) {M : Matrix (n × Option n) (n × Option n) ℂ}
    (hM : M ∈ unitaryGroup (n × Option n) ℂ) (t₁ t : ℝ) :
    measuredComposite U M t₁ t ∈ unitaryGroup (n × Option n) ℂ := by
  have h1 : (1 : Matrix (Option n) (Option n) ℂ) ∈ unitaryGroup (Option n) ℂ := one_mem _
  have hk : ∀ A, A ∈ unitaryGroup n ℂ →
      A ⊗ₖ (1 : Matrix (Option n) (Option n) ℂ) ∈ unitaryGroup (n × Option n) ℂ :=
    fun A hA => kronecker_mem_unitary hA h1
  unfold measuredComposite measuredEvolution
  split_ifs
  · exact hk _ (hU t)
  · refine mul_mem (hk _ (mul_mem (hU t) ?_)) (mul_mem hM (hk _ (hU t₁)))
    exact Unitary.star_mem (hU t₁)

namespace GenStochasticProcess

/-- The system's generalized stochastic process when it evolves by `U t` and is measured by
`M` at time `t₁ > 0`. -/
noncomputable def measuredAt (U : ℝ → Matrix n n ℂ) (hU : ∀ t, U t ∈ unitaryGroup n ℂ)
    (h0 : U 0 = 1) (M : Matrix (n × Option n) (n × Option n) ℂ)
    (hM : M ∈ unitaryGroup (n × Option n) ℂ) (t₁ : ℝ) (ht₁ : 0 < t₁) :
    GenStochasticProcess n where
  Γ t := pointerMarginal (measuredComposite U M t₁ t)
  stochastic t _ :=
    IsUnitaryDilation.mem_colStochastic ⟨measuredComposite_mem_unitaryGroup hU hM t₁ t,
      fun _ _ => rfl⟩
  init := by
    rw [measuredComposite, ite_eq_left_of_eq_true _ _ (eq_true ht₁), pointerMarginal_kron_one, h0,
      normSqMatrix_one]

variable {U : ℝ → Matrix n n ℂ} {hU : ∀ t, U t ∈ unitaryGroup n ℂ} {h0 : U 0 = 1}
  {M : Matrix (n × Option n) (n × Option n) ℂ} {hM : M ∈ unitaryGroup (n × Option n) ℂ}
  {t₁ : ℝ} {ht₁ : 0 < t₁}

/-- Before the measurement, the process is the unitary one. -/
theorem measuredAt_Γ_of_lt {t : ℝ} (ht : t < t₁) :
    (measuredAt U hU h0 M hM t₁ ht₁).Γ t = normSqMatrix (U t) := by
  simp only [measuredAt, measuredComposite, ht, ite_true, pointerMarginal_kron_one]

/-- After the measurement, `Γ(t) = |U(t) U(t₁)†|² · |U(t₁)|²`. -/
theorem measuredAt_Γ_of_le (hMV : IsIdealMeasurement 1 M) {t : ℝ} (ht : t₁ ≤ t) :
    (measuredAt U hU h0 M hM t₁ ht₁).Γ t =
      normSqMatrix (U t * (U t₁)ᴴ) * normSqMatrix (U t₁) := by
  simp only [measuredAt, measuredComposite, not_lt.mpr ht, ite_false,
    hMV.pointerMarginal_measuredEvolution, Matrix.mul_one, conjTranspose_one, Matrix.one_mul]

/-- **Collapse as a division event.** Measuring the configuration at `t₁ > 0` makes `t₁` a
division event of the system's process, whatever the unitary dynamics `U`. -/
theorem measuredAt_isDivisionEvent (hMV : IsIdealMeasurement 1 M) :
    (measuredAt U hU h0 M hM t₁ ht₁).IsDivisionEvent t₁ := by
  refine ⟨ht₁.le, fun t => normSqMatrix (U t * (U t₁)ᴴ), fun t ht => ⟨?_, ?_⟩⟩
  · exact normSqMatrix_mem_colStochastic (mul_mem (hU t) (Unitary.star_mem (hU t₁)))
  · have h : U t₁ * (U t₁)ᴴ = 1 := mem_unitaryGroup_iff.mp (hU t₁)
    rw [measuredAt_Γ_of_le hMV ht, measuredAt_Γ_of_le hMV le_rfl, h, normSqMatrix_one,
      Matrix.one_mul]

end GenStochasticProcess

end ISM
