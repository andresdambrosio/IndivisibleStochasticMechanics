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
is unitary (`U_mem_unitaryGroup`) and that `U 0 = 1` (`U_zero`). With that, the previous
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

## Exercises

1. (Paper) Show that $t'=\pi/2$ **is** a division event. Hint: $\Gamma(\pi/2)$ is a
   permutation, so it has a stochastic inverse.
2. (Paper) Show that **no** $t' \in (0, \pi/2)$ is a division event. Hint: write
   $\Gamma(t) = \tfrac12\begin{pmatrix}1+\lambda & 1-\lambda\\ 1-\lambda & 1+\lambda\end{pmatrix}$
   with $\lambda = \cos 2t$, and use exercise 2 of chapter 4.
3. (Lean) Formalize the two previous exercises. It is an open task on the roadmap.
4. (To think about) At $\pi/2$ the system "restarts". Is it a coincidence that this
   happens exactly when $U(\pi/2)$ is, up to phases, a permutation?
