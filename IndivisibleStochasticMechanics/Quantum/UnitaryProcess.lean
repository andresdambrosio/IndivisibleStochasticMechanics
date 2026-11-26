/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Stochastic.Indivisible
public import IndivisibleStochasticMechanics.Stochastic.Unistochastic

/-!
# Unitary evolution induces a generalized stochastic process

This is the *quantum → stochastic* half of the stochastic-quantum correspondence. Given a
unitary time evolution `U t` in a fixed orthonormal basis (labelled by the configurations
`n`), the matrices

  `Γ t i j = ‖U t i j‖²`

are column-stochastic and satisfy `Γ 0 = 1`, so they define a `GenStochasticProcess`.
Physically, `Γ t i j` is the Born-rule probability of finding configuration `i` at time
`t`, given that the system was in configuration `j` at time `0`.

## Main definitions

* `ISM.GenStochasticProcess.ofUnitary`: the process induced by a unitary evolution.

## References

* J. A. Barandes, *The Stochastic-Quantum Correspondence*, arXiv:2302.10778.
-/

@[expose] public section

open Matrix

namespace ISM

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A unitary matrix is a Born representation of the matrix of its squared moduli,
which is therefore unistochastic. -/
theorem isUnistochastic_normSq {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    IsUnistochastic (Matrix.of fun i j => ‖U i j‖ ^ 2) :=
  ⟨U, hU, fun _ _ => rfl⟩

namespace GenStochasticProcess

/-- The generalized stochastic process induced by a unitary evolution `U` with `U 0 = 1`:
`Γ t i j = ‖U t i j‖²`. -/
noncomputable def ofUnitary (U : ℝ → Matrix n n ℂ) (hU : ∀ t, U t ∈ Matrix.unitaryGroup n ℂ)
    (h0 : U 0 = 1) : GenStochasticProcess n where
  Γ t := Matrix.of fun i j => ‖U t i j‖ ^ 2
  stochastic t _ := (isUnistochastic_normSq (hU t)).mem_colStochastic
  init := by
    ext i j
    by_cases h : i = j <;> simp [h0, Matrix.one_apply, h]

@[simp]
theorem ofUnitary_Γ_apply (U : ℝ → Matrix n n ℂ) (hU : ∀ t, U t ∈ Matrix.unitaryGroup n ℂ)
    (h0 : U 0 = 1) (t : ℝ) (i j : n) :
    (ofUnitary U hU h0).Γ t i j = ‖U t i j‖ ^ 2 :=
  rfl

end GenStochasticProcess

end ISM
