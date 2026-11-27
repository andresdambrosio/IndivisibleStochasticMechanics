# 6. The indivisible qubit: interference seen from the stochastic side

> Code: `IndivisibleStochasticMechanics/Examples/Qubit.lean`

This is the project's first result "with physics": a concrete quantum system whose
stochastic process we **prove** to be indivisible.

The thesis that interference and indivisibility are two faces of the same phenomenon is
Barandes' ([Barandes, 2023a](https://arxiv.org/abs/2302.10778)). The concrete example,
with this Hamiltonian and these times, was put together for this course, and the formal
proof in Lean is ours.

## The system

Two configurations, $\mathcal{C} = \{0, 1\}$, with Hamiltonian $H = \sigma_x$. The
evolution is

$$U(t) = e^{-it\sigma_x} = \cos t\,\mathbb{1} - i\sin t\,\sigma_x = \begin{pmatrix}\cos t & -i\sin t\\ -i\sin t & \cos t\end{pmatrix},$$

and the Born rule gives

$$\Gamma(t) = \begin{pmatrix}\cos^2 t & \sin^2 t\\ \sin^2 t & \cos^2 t\end{pmatrix}.$$

These are the dynamics of **Rabi oscillations**
([Rabi, 1937](https://doi.org/10.1103/PhysRev.51.652)): the system goes from $0$ to $1$
and back.

## Three key times

| $t$ | $\Gamma(t)$ | Interpretation |
|---|---|---|
| $0$ | $\begin{pmatrix}1&0\\0&1\end{pmatrix}$ | nothing has happened |
| $\pi/4$ | $\begin{pmatrix}1/2&1/2\\1/2&1/2\end{pmatrix}$ | complete mixing: the current configuration says nothing about the initial one |
| $\pi/2$ | $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ | deterministic swap: $0 \to 1$ and $1 \to 0$ with certainty |

## The argument

**Theorem.** $t' = \pi/4$ is not a division event. Hence the process is indivisible.

*Proof.* Suppose it were. Then there would be a matrix $\Delta$ with
$\Gamma(\pi/2) = \Delta\,\Gamma(\pi/4)$. But the two columns of $\Gamma(\pi/4)$ are equal,
both $(1/2,1/2)^T$. The columns of $\Delta\,\Gamma(\pi/4)$ are $\Delta$ applied to the
columns of $\Gamma(\pi/4)$, so they are also equal to each other. And the columns of
$\Gamma(\pi/2)$ are $(0,1)^T$ and $(1,0)^T$, which are different. Contradiction.
$\blacksquare$

There is a notable detail: **$\Delta$ does not even need to be stochastic**. No linear law
can "unmix" a distribution that has already forgotten the initial condition.

## What it means physically

At $\pi/4$ the system is in $0$ or in $1$ with probability $1/2$, *whatever* the initial
configuration. If the process were Markovian, the configuration at $\pi/4$ would be all
that matters for the future, and the system would have lost forever the memory of where
it started. Yet at $\pi/2$ it "remembers" perfectly: the outcome depends with certainty on
the initial configuration.

In quantum language, that is **interference**: amplitudes recombine coherently. In
stochastic language, it is **indivisibility**: the laws condition on time $0$, not on
time $\pi/4$. They are two descriptions of the same phenomenon, and that is Barandes'
thesis in a concrete case.

## In Lean

The unitary evolution:

```lean
noncomputable def U (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos t : ℂ), -I * Real.sin t; -I * Real.sin t, Real.cos t]
```

`!![a, b; c, d]` is Mathlib's notation for explicitly written matrices. We prove that it
is unitary (`U_mem_unitaryGroup`) and that `U 0 = 1` (`U_zero`). We also prove that this
explicit matrix really is the exponential of the previous chapter,
`U t = hamiltonianEvolution σx t` (`U_eq_hamiltonianEvolution`). The proof diagonalizes
$\sigma_x = P\,\mathrm{diag}(1,-1)\,P^{-1}$ with $P = \begin{pmatrix}1&1\\1&-1\end{pmatrix}$,
so that $e^{-it\sigma_x} = P\,\mathrm{diag}(e^{-it}, e^{it})\,P^{-1}$, and then uses
$e^{\pm it} = \cos t \pm i \sin t$. With that, the previous
chapter gives us the process for free:

```lean
noncomputable def process : GenStochasticProcess (Fin 2) :=
  GenStochasticProcess.ofUnitary U U_mem_unitaryGroup U_zero
```

We compute $\Gamma(t)$ explicitly (`process_Γ`), and then comes the central theorem:

```lean
theorem not_isDivisionEvent_pi_div_four : ¬ process.IsDivisionEvent (Real.pi / 4) := by
  rintro ⟨-, Δ, hΔ⟩
  have h := (hΔ (Real.pi / 2) (by linarith [Real.pi_pos])).2
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp [process_Γ, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  linarith
```

Line by line:
1. `rintro ⟨-, Δ, hΔ⟩`: "suppose it is a division event, with witness $\Delta$".
2. `have h := ...`: we apply the hypothesis at $t = \pi/2$, after checking that
   $\pi/2 \geq \pi/4$.
3. `h00`, `h01`: we look at the $(0,0)$ and $(0,1)$ entries of the matrix equality.
4. `simp`: substitutes the concrete values. The entries become
   - $(0,0)$: $0 = \tfrac12\Delta_{00} + \tfrac12\Delta_{01}$
   - $(0,1)$: $1 = \tfrac12\Delta_{00} + \tfrac12\Delta_{01}$
5. `linarith`: from these, $0 = 1$, which is absurd.

It is exactly the "equal columns" argument on paper, restricted to the first row.
Finally:

```lean
theorem process_isIndivisible : process.IsIndivisible := fun h =>
  not_isDivisionEvent_pi_div_four (h _ (by positivity))
```

"If it were divisible, $\pi/4$ would be a division event, and we just saw that it is
not."

## All the division events

The argument for $\pi/4$ used that the columns of $\Gamma(\pi/4)$ are equal. Other times
need a different argument, and it gives the complete answer.

**Theorem.** $t' \geq 0$ is a division event of the qubit if and only if $t'$ is a
multiple of $\pi/2$: $t' \in \{0, \pi/2, \pi, 3\pi/2, \dots\}$.

*Proof.* If $t' = k\pi/2$, then $\Gamma(t')$ is the identity ($k$ even) or the swap
($k$ odd). Either way $\Gamma(t')^2 = \mathbb{1}$, so $\Delta(t \leftarrow t') = \Gamma(t)\,\Gamma(t')$
works: it is a product of stochastic matrices, hence stochastic, and
$\Delta\,\Gamma(t') = \Gamma(t)\,\Gamma(t')^2 = \Gamma(t)$.

If $t'$ is not a multiple of $\pi/2$, then $c = \cos^2 t'$ and $s = \sin^2 t'$ are both
strictly positive. Take a later time $t \geq t'$ where the system has swapped,
$\Gamma(t) = \begin{pmatrix}0&1\\1&0\end{pmatrix}$ (any $t = m\pi + \pi/2$ with $m$ large
enough). The first row of $\Gamma(t) = \Delta\,\Gamma(t')$ reads

$$0 = \Delta_{00}\,c + \Delta_{01}\,s, \qquad 1 = \Delta_{00}\,s + \Delta_{01}\,c.$$

$\Delta$ is stochastic, so its entries are nonnegative. In the first equation a sum of
nonnegative terms is $0$, and $c, s > 0$, so $\Delta_{00} = \Delta_{01} = 0$. The second
equation then says $1 = 0$. $\blacksquare$

Here, unlike at $\pi/4$, stochasticity of $\Delta$ is essential. Whenever
$\cos 2t' \neq 0$, which is the determinant of $\Gamma(t')$, the inverse exists and
$\Delta = \Gamma(t)\,\Gamma(t')^{-1}$ solves the equation. It just has negative entries: it
is a valid *linear* law, but not a *stochastic* one.

The picture is clear. The process "restarts" exactly at the times when $\Gamma$ is a
permutation, that is, when the configuration at $t'$ determines the initial one. Between
those times it is indivisible. The characterization is a direct computation done for this
course; the general idea that division events are where the process can be restarted
is Barandes' ([Barandes, 2023a](https://arxiv.org/abs/2302.10778)).

In Lean:

```lean
theorem isDivisionEvent_iff_exists_nat (t' : ℝ) :
    process.IsDivisionEvent t' ↔ ∃ k : ℕ, t' = k * (Real.pi / 2)

theorem isDivisionEvent_pi_div_two : process.IsDivisionEvent (Real.pi / 2)

theorem not_isDivisionEvent_of_mem_Ioo {t' : ℝ} (ht : t' ∈ Set.Ioo 0 (Real.pi / 2)) :
    ¬ process.IsDivisionEvent t'
```

The core is `isDivisionEvent_iff`, which states the condition as $\sin 2t' = 0$
(recall $\sin 2t' = 2 \sin t' \cos t'$). The proof follows the paper argument: the later
time is `m * π + π / 2` with `m = ⌈t' / π⌉₊` (the ceiling, a natural number), and
`nonneg_of_mem_colStochastic` gives the nonnegative entries of $\Delta$.

## Exercises

1. (Paper) Give a second proof that no $t' \in (0, \pi/2)$ other than $\pi/4$ is a
   division event. Write
   $\Gamma(t) = \tfrac12\begin{pmatrix}1+\lambda & 1-\lambda\\ 1-\lambda & 1+\lambda\end{pmatrix}$
   with $\lambda = \cos 2t$, compute $\Gamma(t)\,\Gamma(t')^{-1}$, and use exercise 2 of
   chapter 4.
2. (Paper) Compute $\Delta = \Gamma(\pi/2)\,\Gamma(\pi/6)^{-1}$ explicitly and find its
   negative entries.
3. (Lean) Prove that $\Gamma$ has period $\pi$: `process.Γ (t + Real.pi) = process.Γ t`.
   Hint: `process_Γ`, `Real.cos_add_pi`, `Real.sin_add_pi`.
4. (To think about) At $\pi/2$ the system "restarts". Is it a coincidence that this
   happens exactly when $U(\pi/2)$ is, up to phases, a permutation?
