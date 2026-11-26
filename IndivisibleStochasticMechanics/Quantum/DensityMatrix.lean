/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Quantum.UnitaryProcess
public import IndivisibleStochasticMechanics.ForMathlib.Matrix.Unitary

/-!
# Density matrices from the stochastic side

In Barandes' correspondence the density matrix is a *derived* object. Given a Born
representation `Γᵢⱼ = ‖Θᵢⱼ‖²` and a probability distribution `p` over the initial
configurations, define

  `ρ = Θ · diag(p) · Θᴴ`.

Then `ρ` is a genuine density matrix (positive semidefinite, trace one), and its
**diagonal is exactly the stochastic distribution** `Γ p`. Its off-diagonal entries carry
no extra probabilities; they are the coherences that make interference visible in the
Hilbert-space picture.

For a unitary process `Θ = U(t)` this is the textbook evolution
`ρ(t) = U(t) ρ(0) U(t)ᴴ` of the mixture `ρ(0) = diag(p)`.

## Main results

* `ISM.bornDensity_apply_self`: `ρᵢᵢ = (Γ p)ᵢ`.
* `ISM.bornDensity_isDensityMatrix`: `ρ` is a density matrix.
* `ISM.GenStochasticProcess.ofUnitary_evolve_eq_diag`: for a unitary process, the
  stochastic distribution at time `t` is the diagonal of `U(t) diag(p₀) U(t)ᴴ`.

## References

* J. A. Barandes, *The Stochastic-Quantum Correspondence*, arXiv:2302.10778.
-/

@[expose] public section

open Matrix ComplexOrder

namespace ISM

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A density matrix: positive semidefinite with trace one. -/
def IsDensityMatrix (ρ : Matrix n n ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- The density matrix `Θ · diag(p) · Θᴴ` built from a Born representation `Θ` and a
distribution `p` over initial configurations. -/
noncomputable def bornDensity (Θ : Matrix n n ℂ) (p : n → ℝ) : Matrix n n ℂ :=
  Θ * diagonal (fun j => (p j : ℂ)) * Θᴴ

/-- The diagonal of the Born density matrix is the stochastic distribution `Γ p`. -/
theorem bornDensity_apply_self {Γ : Matrix n n ℝ} {Θ : Matrix n n ℂ} (h : IsBornRep Γ Θ)
    (p : n → ℝ) (i : n) : bornDensity Θ p i i = ((Γ *ᵥ p) i : ℂ) := by
  rw [bornDensity, Matrix.mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, Complex.star_def, Matrix.mulVec, dotProduct, h i]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.mul_conj']
  ring

theorem bornDensity_posSemidef (Θ : Matrix n n ℂ) {p : n → ℝ} (hp : ∀ i, 0 ≤ p i) :
    (bornDensity Θ p).PosSemidef :=
  (posSemidef_diagonal_iff.mpr fun i =>
    Complex.zero_le_real.mpr (hp i)).mul_mul_conjTranspose_same Θ

/-- The Born density matrix of a stochastic matrix and a probability distribution is a
density matrix. -/
theorem bornDensity_isDensityMatrix {Γ : Matrix n n ℝ} {Θ : Matrix n n ℂ}
    (h : IsBornRep Γ Θ) (hΓ : Γ ∈ colStochastic ℝ n) {p : n → ℝ} (hp : IsProbDist p) :
    IsDensityMatrix (bornDensity Θ p) := by
  refine ⟨bornDensity_posSemidef Θ hp.nonneg, ?_⟩
  rw [Matrix.trace]
  simp only [diag_apply, bornDensity_apply_self h]
  exact_mod_cast (hp.mulVec hΓ).sum_eq_one

/-- For a unitary process, the stochastic distribution at time `t` is the diagonal of the
textbook density matrix `U(t) diag(p₀) U(t)ᴴ`. -/
theorem GenStochasticProcess.ofUnitary_evolve_eq_diag (U : ℝ → Matrix n n ℂ)
    (hU : ∀ t, U t ∈ Matrix.unitaryGroup n ℂ) (h0 : U 0 = 1) (p₀ : n → ℝ) (t : ℝ) (i : n) :
    ((ofUnitary U hU h0).evolve p₀ t i : ℂ) = bornDensity (U t) p₀ i i :=
  (bornDensity_apply_self (fun _ _ => rfl) p₀ i).symm

end ISM
