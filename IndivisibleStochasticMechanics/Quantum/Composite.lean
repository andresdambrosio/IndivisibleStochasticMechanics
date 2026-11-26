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


section LocalOperations

variable {A B E : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype E] [DecidableEq E]

/-- Bob's local operation: a unitary `N` on his system and his own ancilla `E`. -/
def bobLocal (N : Matrix (B × E) (B × E) ℂ) : Matrix ((A × B) × E) ((A × B) × E) ℂ :=
  of fun r c => (if r.1.1 = c.1.1 then 1 else 0) * N (r.1.2, r.2) (c.1.2, c.2)

/-- Alice's transition probabilities after a joint evolution `Ψ`, summing over Bob's system
and ancilla, starting from configuration `j` and ancilla state `e₀`. -/
noncomputable def aliceMarginal (Ψ : Matrix ((A × B) × E) ((A × B) × E) ℂ) (j : A × B)
    (e₀ : E) (i : A) : ℝ :=
  ∑ p : B × E, ‖Ψ ((i, p.1), p.2) (j, e₀)‖ ^ 2

omit [DecidableEq B] in
/-- The amplitude after Bob's local operation is `N` applied to the vector
`(b, e) ↦ Θ (i, b) j · δ(e, e₀)`. -/
theorem bobLocal_mul_apply (N : Matrix (B × E) (B × E) ℂ) (Θ : Matrix (A × B) (A × B) ℂ)
    (j : A × B) (e₀ : E) (i : A) (p : B × E) :
    (bobLocal (A := A) N * (Θ ⊗ₖ (1 : Matrix E E ℂ))) ((i, p.1), p.2) (j, e₀) =
      (N *ᵥ fun q : B × E => Θ (i, q.1) j * (1 : Matrix E E ℂ) q.2 e₀) p := by
  rw [Matrix.mul_apply, mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp [bobLocal, Fintype.sum_prod_type]
  · intro k _ hk
    simp [bobLocal, Ne.symm hk]
  · simp

/-- **No signalling, for any local operation of Bob.** Whatever unitary Bob applies to his
system and his own ancilla (in particular, any measurement with his own apparatus), Alice's
transition probabilities do not change. -/
theorem aliceMarginal_bobLocal {N : Matrix (B × E) (B × E) ℂ}
    (hN : N ∈ unitaryGroup (B × E) ℂ) (Θ : Matrix (A × B) (A × B) ℂ) (j : A × B) (e₀ : E)
    (i : A) :
    aliceMarginal (bobLocal (A := A) N * (Θ ⊗ₖ (1 : Matrix E E ℂ))) j e₀ i = ∑ b, ‖Θ (i, b) j‖ ^ 2 := by
  simp only [aliceMarginal, bobLocal_mul_apply]
  rw [sum_norm_sq_mulVec_of_mem_unitaryGroup hN, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single e₀]
  · simp
  · intro e _ he; simp [one_apply_ne he]
  · simp

/-- **No signalling for local measurements.** If Bob measures his system with an ideal
apparatus (chapter 9), Alice's transition probabilities are unchanged. -/
theorem aliceMarginal_of_isIdealMeasurement {W : Matrix B B ℂ}
    {N : Matrix (B × Option B) (B × Option B) ℂ} (hN : IsIdealMeasurement W N)
    (Θ : Matrix (A × B) (A × B) ℂ) (j : A × B) (i : A) :
    aliceMarginal (bobLocal (A := A) N * (Θ ⊗ₖ (1 : Matrix (Option B) (Option B) ℂ))) j none
      i =
      ∑ b, ‖Θ (i, b) j‖ ^ 2 :=
  aliceMarginal_bobLocal hN.1 Θ j none i

end LocalOperations

end ISM
