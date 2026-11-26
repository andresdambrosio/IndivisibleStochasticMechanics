# 3. Probabilities and stochastic matrices

> Code: `IndivisibleStochasticMechanics/Stochastic/Basic.lean`

## The physical idea

The material in this chapter is standard probability. The column convention is Barandes'
([Barandes, 2023a](https://arxiv.org/abs/2302.10778)).

The system has a finite **configuration space** $\mathcal{C} = \{1, \dots, N\}$. These
could be the positions of a particle on a lattice, the two states of a bit, and so on. At
each instant the system is in *one* configuration. We do not know which, so we describe
our knowledge with a probability distribution $p_i(t)$.

The dynamics is given by the **transition probabilities**

$$\Gamma_{ij}(t) = P(\text{being in } i \text{ at time } t \mid \text{was in } j \text{ at time } 0).$$

## The mathematics

**Definition (probability distribution).** $p \in \mathbb{R}^N$ is a distribution if
$p_i \geq 0$ for every $i$ and $\sum_i p_i = 1$.

**Definition (column-stochastic matrix).** $\Gamma \in \mathbb{R}^{N\times N}$ is
stochastic if $\Gamma_{ij} \geq 0$ for all $i,j$ and every column sums to one:
$\sum_i \Gamma_{ij} = 1$ for every $j$.

The column condition says that, starting from $j$, the system ends up in *some*
configuration with probability 1.

By the law of total probability, the distribution evolves as

$$p_i(t) = \sum_j \Gamma_{ij}(t)\, p_j(0), \qquad\text{that is}\qquad p(t) = \Gamma(t)\,p(0).$$

**Proposition.** If $\Gamma$ is stochastic and $p$ is a distribution, then $\Gamma p$ is a
distribution.

*Proof.* Nonnegativity holds because it is a sum of products of nonnegative numbers. For
the sum:
$$\sum_i (\Gamma p)_i = \sum_i \sum_j \Gamma_{ij}\,p_j = \sum_j p_j \underbrace{\sum_i \Gamma_{ij}}_{=1} = \sum_j p_j = 1. \qquad\blacksquare$$

**Fact.** The product of two stochastic matrices is stochastic, and the identity is
stochastic. In algebraic language, stochastic matrices form a **monoid**. Physically, the
identity is "nothing happens" and the product is "chaining two evolutions".

## In Lean

We define the probability distribution ourselves:

```lean
structure IsProbDist (p : n → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ p i
  sum_eq_one : ∑ i, p i = 1
```

For stochastic matrices we use Mathlib's definition: `Γ ∈ colStochastic ℝ n`. Mathlib
defines it as a `Submonoid` of matrices, so the "Fact" above comes for free: `one_mem` and
`mul_mem`.

The proposition takes four lines:

```lean
theorem IsProbDist.mulVec [DecidableEq n] {Γ : Matrix n n ℝ} (hΓ : Γ ∈ colStochastic ℝ n)
    {p : n → ℝ} (hp : IsProbDist p) : IsProbDist (Γ *ᵥ p) where
  nonneg := nonneg_mulVec_of_mem_colStochastic hΓ hp.nonneg
  sum_eq_one := by rw [sum_mulVec_of_mem_colStochastic hΓ, hp.sum_eq_one]
```

- `Γ *ᵥ p` is the matrix-vector product.
- `nonneg := ...` proves the first condition with a Mathlib lemma.
- `sum_eq_one := ...` uses another Mathlib lemma, which says
  $\sum_i (\Gamma p)_i = \sum_i p_i$, and then the hypothesis $\sum_i p_i = 1$.

It is the same proof as on paper. Someone in Mathlib already did the part where the sums
are swapped.

## Exercises

1. (Paper) Prove that if $\Gamma$ is stochastic, then $0 \leq \Gamma_{ij} \leq 1$.
   (In Mathlib: `le_one_of_mem_colStochastic`.)
2. (Paper) Why does Barandes use the *column* convention rather than the *row* one? What
   changes in the formula $p(t) = \Gamma(t)p(0)$?
3. (Lean) State and prove that every permutation matrix is stochastic. Hint: Mathlib
   already has `permMatrix_mem_colStochastic`. Find it and use it.
