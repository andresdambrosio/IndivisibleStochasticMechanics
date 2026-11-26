# 4. Indivisible processes and division events

> Code: `IndivisibleStochasticMechanics/Stochastic/Indivisible.lean`

## The physical idea

In a probability course, a stochastic process is usually **Markovian**: the future
depends only on the present. So to go from $0$ to $t$ we can stop at any intermediate
$t'$:

$$\Gamma(t\leftarrow 0) = \Gamma(t\leftarrow t')\,\Gamma(t'\leftarrow 0), \qquad 0 \le t' \le t,$$

with $\Gamma(t\leftarrow t')$ stochastic. This is called **divisibility**.

Barandes' key observation ([Barandes, 2023a](https://arxiv.org/abs/2302.10778),
[Barandes, 2025](https://arxiv.org/abs/2507.21192)) is that **nothing in probability
theory forces this to happen**. A process is defined by its conditional probabilities
with respect to the initial time, $\Gamma(t\leftarrow 0)$. That there also exist
stochastic $\Gamma(t\leftarrow t')$ composing them is an *additional* property, which may
or may not hold.

- If it holds at a particular time $t'$, we say $t'$ is a **division event**: the process
  "restarts" there. The term is Barandes'.
- If it does not hold at every time, the process is **indivisible**.

Barandes argues that quantum systems are precisely indivisible processes, and that
division events arise physically when there is **decoherence** or **measurement**.

Divisibility as a criterion of "Markovianity" is not specific to Barandes. In the theory
of open quantum systems, the divisibility of quantum channels is studied
([Wolf and Cirac, 2008](https://arxiv.org/abs/math-ph/0611057)) and used to define
non-Markovianity ([Rivas, Huelga and Plenio, 2014](https://arxiv.org/abs/1405.0303)).
What is specific to Barandes is taking indivisible *stochastic* matrices as the
fundamental description of quantum systems.

## The mathematics

**Definition (generalized stochastic process).** A family of matrices
$\Gamma(t) := \Gamma(t\leftarrow 0)$, for $t \geq 0$, such that:
1. $\Gamma(t)$ is stochastic for every $t \geq 0$;
2. $\Gamma(0) = \mathbb{1}$: at time zero nothing has happened.

**Definition (division event, formalized from
[Barandes, 2023a](https://arxiv.org/abs/2302.10778)).** $t' \geq 0$ is a division event if
there is a family $\Delta(t)$ with $\Delta(t)$ stochastic and
$$\Gamma(t) = \Delta(t)\,\Gamma(t') \qquad \text{for every } t \ge t'.$$
Here $\Delta(t)$ plays the role of $\Gamma(t \leftarrow t')$. Asking for *one* family
$\Delta(t)$ that works for all $t \ge t'$ is an interpretive choice we made when
formalizing, and it is recorded in `TRUSTED.md`.

**Definition.** The process is **divisible** if every $t' \geq 0$ is a division event,
and **indivisible** if it is not.

**Proposition.** $t' = 0$ is always a division event.

*Proof.* Take $\Delta(t) = \Gamma(t)$. Since $\Gamma(0) = \mathbb{1}$, we have
$\Gamma(t) = \Gamma(t)\cdot\mathbb{1}$. $\blacksquare$

## In Lean

```lean
structure GenStochasticProcess (n : Type*) [Fintype n] [DecidableEq n] where
  Γ : ℝ → Matrix n n ℝ
  stochastic : ∀ t, 0 ≤ t → Γ t ∈ colStochastic ℝ n
  init : Γ 0 = 1
```

A `structure` that is not a `Prop` is an "object with data". A process *is* a function
`Γ` from times to matrices, *together with* the proofs that it is stochastic and that it
starts at the identity. You cannot build a process without supplying those proofs.

```lean
def IsDivisionEvent (t' : ℝ) : Prop :=
  0 ≤ t' ∧ ∃ Δ : ℝ → Matrix n n ℝ,
    ∀ t, t' ≤ t → Δ t ∈ colStochastic ℝ n ∧ P.Γ t = Δ t * P.Γ t'

def IsDivisible : Prop := ∀ t', 0 ≤ t' → P.IsDivisionEvent t'
def IsIndivisible : Prop := ¬ P.IsDivisible
```

The translation is literal. `¬` is "not", `∃` is "there exists" and `∀` is "for all".

```lean
theorem isDivisionEvent_zero : P.IsDivisionEvent 0 :=
  ⟨le_rfl, P.Γ, fun t ht => ⟨P.stochastic t ht, by simp [P.init]⟩⟩
```

The angle brackets `⟨ ... ⟩` assemble the proof piece by piece, in the same order as the
definition:
- `le_rfl` proves $0 \le 0$;
- `P.Γ` is the witness $\Delta$;
- for each $t$, `P.stochastic t ht` proves that $\Delta(t)$ is stochastic, and
  `by simp [P.init]` proves $\Gamma(t) = \Gamma(t)\,\Gamma(0)$ using
  $\Gamma(0)=\mathbb{1}$.

## A subtlety: what the definition does *not* say

A generalized process specifies only $\Gamma(t\leftarrow 0)$. It does **not** specify
joint probabilities at several times, such as
$P(i \text{ at } t_2,\ k \text{ at } t_1 \mid j \text{ at } 0)$. This is a deliberate
choice by Barandes ([Barandes, 2023a](https://arxiv.org/abs/2302.10778)), and it is one of
the open questions of Part IV.

## Exercises

1. (Paper) Show that if $\Gamma(t) = e^{tL}$ for a matrix $L$ whose columns sum to zero
   and whose off-diagonal entries are nonnegative (a *Markov generator*), the process is
   divisible.
2. (Paper) If $\Gamma(t')$ is invertible, what is the only possible candidate for
   $\Delta(t)$? What condition must it satisfy for $t'$ to be a division event?
3. (Lean) Prove that if $\Gamma(t) = \mathbb{1}$ for every $t$, the process is divisible.
