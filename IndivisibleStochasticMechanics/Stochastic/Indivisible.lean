/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Stochastic.Basic

/-!
# Generalized (indivisible) stochastic processes

Barandes' central object is a stochastic process specified only by its *cumulative*
transition matrices `Γ(t ← 0)` from a fixed initial time, **without** assuming that they
factor through intermediate times. A textbook Markov process is *divisible*: for every
`0 ≤ t' ≤ t` there is a stochastic `Γ(t ← t')` with `Γ(t ← 0) = Γ(t ← t') * Γ(t' ← 0)`.
A generic indivisible process admits such factorizations only at special times, called
*division events*.

## Main definitions

* `ISM.GenStochasticProcess`: transition matrices `Γ t = Γ(t ← 0)` for `t ≥ 0`.
* `ISM.GenStochasticProcess.IsDivisionEvent`: `t'` is a time through which the dynamics
  factor stochastically.
* `ISM.GenStochasticProcess.IsDivisible`: every time is a division event (Markovian case).

## References

* J. A. Barandes, *The Stochastic-Quantum Correspondence*, arXiv:2302.10778, §3.
-/

@[expose] public section

open Matrix

namespace ISM

/-- A generalized stochastic process on a finite configuration space `n`, given by its
cumulative transition matrices `Γ t = Γ(t ← 0)`. -/
structure GenStochasticProcess (n : Type*) [Fintype n] [DecidableEq n] where
  /-- `Γ t i j = P(i at time t | j at time 0)`. -/
  Γ : ℝ → Matrix n n ℝ
  stochastic : ∀ t, 0 ≤ t → Γ t ∈ colStochastic ℝ n
  init : Γ 0 = 1

namespace GenStochasticProcess

variable {n : Type*} [Fintype n] [DecidableEq n] (P : GenStochasticProcess n)

/-- `t'` is a *division event* if for every later time `t` the evolution factors as
`Γ(t ← 0) = Δ(t ← t') * Γ(t' ← 0)` with `Δ(t ← t')` stochastic. -/
def IsDivisionEvent (t' : ℝ) : Prop :=
  0 ≤ t' ∧ ∃ Δ : ℝ → Matrix n n ℝ,
    ∀ t, t' ≤ t → Δ t ∈ colStochastic ℝ n ∧ P.Γ t = Δ t * P.Γ t'

/-- A process is *divisible* (Markovian) if every time is a division event. -/
def IsDivisible : Prop := ∀ t', 0 ≤ t' → P.IsDivisionEvent t'

/-- A process is *indivisible* if it is not divisible. -/
def IsIndivisible : Prop := ¬ P.IsDivisible

/-- The initial time is always a division event: take `Δ = Γ`. -/
theorem isDivisionEvent_zero : P.IsDivisionEvent 0 :=
  ⟨le_rfl, P.Γ, fun t ht => ⟨P.stochastic t ht, by simp [P.init]⟩⟩

/-- Probability distribution at time `t`, starting from `p₀`. -/
def evolve (p₀ : n → ℝ) (t : ℝ) : n → ℝ := P.Γ t *ᵥ p₀

theorem evolve_isProbDist {p₀ : n → ℝ} (hp : IsProbDist p₀) {t : ℝ} (ht : 0 ≤ t) :
    IsProbDist (P.evolve p₀ t) :=
  hp.mulVec (P.stochastic t ht)

end GenStochasticProcess

end ISM
