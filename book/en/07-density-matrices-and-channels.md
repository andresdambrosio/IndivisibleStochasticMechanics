# 7. Density matrices and quantum channels

> Code: `IndivisibleStochasticMechanics/Quantum/DensityMatrix.lean`,
> `IndivisibleStochasticMechanics/Quantum/Channel.lean`

So far we have worked with unitary evolutions and state vectors. Textbook quantum
mechanics uses two more general tools: the **density matrix**, for mixed states, and
**quantum channels**, for open systems, noise and loss of information. This chapter shows
that both have an exact stochastic counterpart.

## Part A: the density matrix as a derived object

### The physical idea

In the usual formulation, the density matrix $\rho$ is *the* state of the system. In
Barandes' ([Barandes, 2023a](https://arxiv.org/abs/2302.10778)) it is a **calculational
tool** built from two ingredients: the Born representation $\Theta$ and the probability
distribution $p$ over initial configurations:

$$\rho = \Theta\,\mathrm{diag}(p)\,\Theta^\dagger .$$

### The mathematics

**Theorem.** If $\Gamma_{ij} = |\Theta_{ij}|^2$, then the diagonal of $\rho$ is the
stochastic distribution:
$$\rho_{ii} = \sum_j \Gamma_{ij}\,p_j = (\Gamma p)_i .$$

*Proof.*
$$\rho_{ii} = \sum_j \Theta_{ij}\,p_j\,\overline{\Theta_{ij}} = \sum_j |\Theta_{ij}|^2 p_j = \sum_j \Gamma_{ij}\,p_j. \qquad\blacksquare$$

**Theorem.** If $\Gamma$ is stochastic and $p$ is a distribution, then $\rho$ is a
genuine density matrix: it is positive semidefinite and has trace 1.

*Proof.* $\mathrm{diag}(p)$ is positive semidefinite because $p_j \ge 0$, and conjugating
by $\Theta$ preserves that property. For the trace,
$\mathrm{tr}\,\rho = \sum_i \rho_{ii} = \sum_i (\Gamma p)_i = 1$ by chapter 3.
$\blacksquare$

**Corollary.** For a unitary process, $\rho(t) = U(t)\,\mathrm{diag}(p_0)\,U(t)^\dagger$ is
*exactly* the textbook evolution of a mixed state, and its diagonal is the stochastic
distribution at time $t$.

### What the diagonal says and what the other entries say

This section is our reading of the results, in line with Barandes'. The diagonal of
$\rho$ contains **all** the probabilistic information about where the system is. The
off-diagonal entries (the *coherences*) are not probabilities of anything. They are the
trace of indivisibility: the information the system needs in order to "remember" its
initial configuration later on.

**Example: the qubit of chapter 6.** If it starts in configuration 0, then
$p_0 = (1, 0)$ and

$$\rho(t) = \begin{pmatrix}\cos^2 t & i\cos t\sin t\\ -i\cos t\sin t & \sin^2 t\end{pmatrix}.$$

At $t = \pi/4$ the diagonal is $(1/2, 1/2)$: complete mixing. But the coherences are
$\pm i/2$, the largest possible value. In a classical mixture they would be zero. That
difference is precisely what lets the system "come back" to a definite configuration at
$t = \pi/2$.

## Part B: quantum channels

### The physical idea

A **quantum channel** describes any possible physical evolution of a system, even when it
interacts with an environment we have no access to. It is written in **Kraus form**
([Kraus, 1971](https://doi.org/10.1016/0003-4916(71)90108-4);
[Choi, 1975](https://doi.org/10.1016/0024-3795(75)90075-0)):
$$\rho \;\mapsto\; \sum_k K_k\,\rho\,K_k^\dagger, \qquad \sum_k K_k^\dagger K_k = \mathbb{1}.$$
A unitary evolution is the case of a single Kraus operator, $K = U$.

### The mathematics

**Theorem (from quantum to stochastic).** Every channel induces a stochastic matrix:
$$\Gamma_{ij} = \sum_k |(K_k)_{ij}|^2 .$$

*Proof.* Each column sums to
$\sum_i\sum_k |(K_k)_{ij}|^2 = \sum_k (K_k^\dagger K_k)_{jj} = \mathbb{1}_{jj} = 1$.
$\blacksquare$

**Theorem.** Applied to a mixture of configurations $\mathrm{diag}(p)$, the channel
produces a matrix with diagonal $\Gamma p$.

**Theorem (from stochastic to quantum).** Every stochastic matrix is the transition
matrix of some quantum channel. This is the standard way of viewing a classical channel
as a quantum one (see for example
[Nielsen and Chuang, 2000](https://doi.org/10.1017/CBO9780511976667)). It suffices to take
the "classical" Kraus operators
$$K_{(a,b)} = \sqrt{\Gamma_{ab}}\;|a\rangle\langle b| ,$$
which take configuration $b$ to $a$ with amplitude $\sqrt{\Gamma_{ab}}$.

*Proof.*
$\sum_{a,b} K_{(a,b)}^\dagger K_{(a,b)} = \sum_{a,b} \Gamma_{ab}\,|b\rangle\langle b| = \sum_b \big(\textstyle\sum_a \Gamma_{ab}\big)|b\rangle\langle b| = \mathbb{1}$,
because the columns sum to 1. Moreover,
$\sum_{a,b} |(K_{(a,b)})_{ij}|^2 = \Gamma_{ij}$. $\blacksquare$

**Conclusion.** For transition statistics from the initial time, quantum channels and
stochastic matrices are the same thing. Compared with chapter 8, this result does not
need a larger configuration space, because channels already include an environment
implicitly.

## In Lean

```lean
noncomputable def bornDensity (Θ : Matrix n n ℂ) (p : n → ℝ) : Matrix n n ℂ :=
  Θ * diagonal (fun j => (p j : ℂ)) * Θᴴ

theorem bornDensity_apply_self {Γ : Matrix n n ℝ} {Θ : Matrix n n ℂ} (h : IsBornRep Γ Θ)
    (p : n → ℝ) (i : n) : bornDensity Θ p i i = ((Γ *ᵥ p) i : ℂ)
```

For positivity we use Mathlib's `PosSemidef`. Over ℂ the partial order has to be turned
on with `open ComplexOrder`, because Mathlib does not enable it by default: the order on
complex numbers is not the one you might expect.

```lean
def IsKrausFamily (K : κ → Matrix n n ℂ) : Prop := ∑ k, (K k)ᴴ * K k = 1

noncomputable def krausTransition (K : κ → Matrix n n ℂ) : Matrix n n ℝ :=
  Matrix.of fun i j => ∑ k, ‖K k i j‖ ^ 2

theorem IsKrausFamily.krausTransition_mem_colStochastic (hK : IsKrausFamily K) :
    krausTransition K ∈ colStochastic ℝ n

theorem krausTransition_classicalKraus (hΓ : Γ ∈ colStochastic ℝ n) :
    krausTransition (classicalKraus Γ) = Γ
```

A useful technical detail: the identity "squared norm of a column = diagonal entry of
$A^\dagger A$" comes up again and again. We put it in `ForMathlib/` as
`Matrix.sum_norm_sq_col_eq_conjTranspose_mul_self`.

## Exercises

1. (Paper) Compute $\rho(t)$ for the qubit with $p_0 = (1/2, 1/2)$. Are there coherences?
   What does that tell you about whether $\pi/4$ is a division event for that initial
   condition?
2. (Paper) The *dephasing channel* (Nielsen and Chuang, ch. 8) has
   $K_0 = \sqrt{1-q}\,\mathbb{1}$ and $K_1 = \sqrt{q}\,\sigma_z$. Compute its $\Gamma$. What
   does it do to the coherences?
3. (Paper) Show that a composition of channels is a channel. Why does this not contradict
   the fact that indivisible processes do not decompose into steps?
4. (Lean) Formalize exercise 2.
