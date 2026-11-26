/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Quantum.Decoherence
public import IndivisibleStochasticMechanics.ForMathlib.Matrix.Stochastic

/-!
# Composite systems

Two systems with configuration spaces `n` and `m` form a composite system with
configuration space `n × m`: a configuration of the whole is a pair of configurations.

* **Independent systems.** If the two systems do not interact, their composite process is
  the Kronecker product `Γ(t) = Γ₁(t) ⊗ Γ₂(t)`, and quantum evolutions `U(t) ⊗ V(t)` give
  exactly that product. A time that divides both factors divides the product.
* **No signalling.** Whatever the joint evolution, a local unitary on the second system
  does not change the transition probabilities of the first. In stochastic language: what
  Bob does cannot be seen in Alice's statistics.

Entanglement, the interesting case in which the systems interact, is illustrated in
`ISM.Examples.BellPair`.

## Main definitions

* `ISM.GenStochasticProcess.prod`: the process of two independent systems.

## Main results

* `ISM.normSqMatrix_kronecker`: `|A ⊗ B|² = |A|² ⊗ |B|²`.
* `ISM.GenStochasticProcess.ofUnitary_kronecker`: independent unitaries give the product
  process.
* `ISM.GenStochasticProcess.prod_isDivisionEvent`: common division events survive.
* `ISM.envMarginal_one_kronecker_mul`: no signalling.

## References

* J. A. Barandes, *The Stochastic-Quantum Correspondence*, arXiv:2302.10778 (composite
  systems and entanglement, §3.9).
* J. A. Barandes, *New Prospects for a Causally Local Formulation of Quantum Theory*,
  arXiv:2402.16935 (locality).
* G. C. Ghirardi, A. Rimini and T. Weber, Lett. Nuovo Cimento 27, 293 (1980),
  doi:10.1007/BF02817189 (the no-signalling theorem of quantum mechanics).
-/

@[expose] public section

open Matrix Kronecker

namespace ISM

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- For independent systems, Born probabilities multiply: `|A ⊗ B|² = |A|² ⊗ |B|²`. -/
theorem normSqMatrix_kronecker (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    normSqMatrix (A ⊗ₖ B) = normSqMatrix A ⊗ₖ normSqMatrix B := by
  ext i j; simp [normSqMatrix, mul_pow]

/-- **No signalling.** A unitary `B` acting only on the second system (Bob) does not change
the transition probabilities of the first system (Alice), whatever the joint evolution `Θ`
that came before. -/
theorem envMarginal_one_kronecker_mul {B : Matrix m m ℂ} (hB : B ∈ unitaryGroup m ℂ)
    (Θ : Matrix (n × m) (n × m) ℂ) (e₀ : m) :
    envMarginal (((1 : Matrix n n ℂ) ⊗ₖ B) * Θ) e₀ = envMarginal Θ e₀ := by
  ext i j
  have h : ∀ e, (((1 : Matrix n n ℂ) ⊗ₖ B) * Θ) (i, e) (j, e₀) =
      (B *ᵥ fun e' => Θ (i, e') (j, e₀)) e := fun e => by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, mulVec, dotProduct]
  simp only [envMarginal, of_apply, h]
  exact sum_norm_sq_mulVec_of_mem_unitaryGroup hB _

namespace GenStochasticProcess

/-- Two systems that evolve independently: the composite process `Γ(t) = Γ₁(t) ⊗ Γ₂(t)`. -/
def prod (P : GenStochasticProcess n) (Q : GenStochasticProcess m) :
    GenStochasticProcess (n × m) where
  Γ t := P.Γ t ⊗ₖ Q.Γ t
  stochastic t ht := kronecker_mem_colStochastic (P.stochastic t ht) (Q.stochastic t ht)
  init := by rw [P.init, Q.init, one_kronecker_one]

/-- A time that divides both independent processes divides the composite one. -/
theorem prod_isDivisionEvent {P : GenStochasticProcess n} {Q : GenStochasticProcess m}
    {t' : ℝ} (hP : P.IsDivisionEvent t') (hQ : Q.IsDivisionEvent t') :
    (P.prod Q).IsDivisionEvent t' := by
  obtain ⟨ht', Δ₁, h₁⟩ := hP
  obtain ⟨-, Δ₂, h₂⟩ := hQ
  refine ⟨ht', fun t => Δ₁ t ⊗ₖ Δ₂ t, fun t ht => ⟨?_, ?_⟩⟩
  · exact kronecker_mem_colStochastic (h₁ t ht).1 (h₂ t ht).1
  · simp only [prod]
    rw [(h₁ t ht).2, (h₂ t ht).2, mul_kronecker_mul]

/-- Two independent divisible (Markovian) processes form a divisible process. -/
theorem prod_isDivisible {P : GenStochasticProcess n} {Q : GenStochasticProcess m}
    (hP : P.IsDivisible) (hQ : Q.IsDivisible) : (P.prod Q).IsDivisible :=
  fun t' ht' => prod_isDivisionEvent (hP t' ht') (hQ t' ht')

/-- Two systems evolving by independent unitaries `U(t) ⊗ V(t)` form the product process. -/
theorem ofUnitary_kronecker {U : ℝ → Matrix n n ℂ} {V : ℝ → Matrix m m ℂ}
    (hU : ∀ t, U t ∈ unitaryGroup n ℂ) (hV : ∀ t, V t ∈ unitaryGroup m ℂ)
    (hU0 : U 0 = 1) (hV0 : V 0 = 1) (t : ℝ) :
    (ofUnitary (fun t => U t ⊗ₖ V t) (fun t => kronecker_mem_unitary (hU t) (hV t))
      (by simp [hU0, hV0])).Γ t = ((ofUnitary U hU hU0).prod (ofUnitary V hV hV0)).Γ t := by
  ext i j; simp [prod, mul_pow]

end GenStochasticProcess

end ISM
