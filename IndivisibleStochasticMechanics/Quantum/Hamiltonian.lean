/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Quantum.UnitaryProcess

/-!
# Hamiltonian evolution `U(t) = exp(-itH)`

In textbook quantum mechanics a closed system with Hamiltonian `H` (Hermitian, `ℏ = 1`)
evolves by `U(t) = exp(-itH)`, the solution of the Schrödinger equation `i U' = H U` with
`U(0) = 1`. Here the exponential is Mathlib's `NormedSpace.exp` on matrices.

We prove that `U(t)` is unitary, that `U(0) = 1`, and the group law
`U(s + t) = U(s) U(t)`. Hence every finite-dimensional Hamiltonian induces a generalized
stochastic process `Γᵢⱼ(t) = |U(t)ᵢⱼ|²` (`GenStochasticProcess.ofHamiltonian`).

The group law holds for `U`, not for `Γ`: in general `Γ(s + t) ≠ Γ(s) Γ(t)`. That gap is
indivisibility (see `ISM.Qubit.isDivisionEvent_iff_exists_nat`).

## Main definitions

* `ISM.hamiltonianEvolution`: `U(t) = exp(-itH)`.
* `ISM.GenStochasticProcess.ofHamiltonian`: the process induced by a Hermitian `H`.

## References

* J. A. Barandes, *The Stochastic-Quantum Correspondence*, arXiv:2302.10778.
-/

@[expose] public section

open Matrix Complex NormedSpace

namespace ISM

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Hamiltonian evolution `U(t) = exp(-itH)`, with `ℏ = 1`. -/
noncomputable def hamiltonianEvolution (H : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  exp ((-(t : ℂ) * I) • H)

theorem hamiltonianEvolution_zero (H : Matrix n n ℂ) : hamiltonianEvolution H 0 = 1 := by
  simp [hamiltonianEvolution]

/-- The group law `U(s + t) = U(s) U(t)`. -/
theorem hamiltonianEvolution_add (H : Matrix n n ℂ) (s t : ℝ) :
    hamiltonianEvolution H (s + t) = hamiltonianEvolution H s * hamiltonianEvolution H t := by
  rw [hamiltonianEvolution, hamiltonianEvolution, hamiltonianEvolution,
    ← Matrix.exp_add_of_commute _ _ ((Commute.refl H).smul_left _ |>.smul_right _)]
  congr 1
  push_cast
  rw [← add_smul]
  ring_nf

/-- For a Hermitian `H`, `U(t)† = U(-t)`. -/
theorem conjTranspose_hamiltonianEvolution {H : Matrix n n ℂ} (hH : H.IsHermitian) (t : ℝ) :
    (hamiltonianEvolution H t)ᴴ = hamiltonianEvolution H (-t) := by
  rw [hamiltonianEvolution, hamiltonianEvolution, ← Matrix.exp_conjTranspose,
    conjTranspose_smul, hH.eq]
  congr 1
  simp [Complex.conj_ofReal]

/-- **Hamiltonian evolution is unitary.** -/
theorem hamiltonianEvolution_mem_unitaryGroup {H : Matrix n n ℂ} (hH : H.IsHermitian) (t : ℝ) :
    hamiltonianEvolution H t ∈ unitaryGroup n ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_hamiltonianEvolution hH,
    ← hamiltonianEvolution_add, neg_add_cancel, hamiltonianEvolution_zero]

/-- `U(s) U(t)† = U(s - t)`. -/
theorem hamiltonianEvolution_mul_conjTranspose {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (s t : ℝ) :
    hamiltonianEvolution H s * (hamiltonianEvolution H t)ᴴ = hamiltonianEvolution H (s - t) := by
  rw [conjTranspose_hamiltonianEvolution hH, ← hamiltonianEvolution_add, sub_eq_add_neg]

namespace GenStochasticProcess

/-- The generalized stochastic process induced by a Hermitian Hamiltonian `H`:
`Γᵢⱼ(t) = |exp(-itH)ᵢⱼ|²`. -/
noncomputable def ofHamiltonian (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    GenStochasticProcess n :=
  ofUnitary (hamiltonianEvolution H) (hamiltonianEvolution_mem_unitaryGroup hH)
    (hamiltonianEvolution_zero H)

@[simp]
theorem ofHamiltonian_Γ_apply (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) (i j : n) :
    (ofHamiltonian H hH).Γ t i j = ‖hamiltonianEvolution H t i j‖ ^ 2 :=
  rfl

end GenStochasticProcess

end ISM
