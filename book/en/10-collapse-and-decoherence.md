# 10. Collapse and decoherence as division events

> Code: `IndivisibleStochasticMechanics/Quantum/Collapse.lean`,
> `IndivisibleStochasticMechanics/Quantum/Decoherence.lean`,
> `IndivisibleStochasticMechanics/Examples/MeasuredQubit.lean` and
> `IndivisibleStochasticMechanics/Examples/DecoheredQubit.lean`

## The problem

Textbook quantum mechanics has **two** dynamical laws:

1. While nobody looks, the state evolves unitarily: $\psi \mapsto U\psi$.
2. When someone measures and gets outcome $a$, the state **collapses** to $v_a$, and from
   there it keeps evolving by the first law.

The second law is strange. It is neither unitary nor linear, and it depends on a notion
of "measurement" that the theory never defines. Many consider this to be *the* problem of
quantum mechanics.

In chapter 9 we saw, following Barandes
([Barandes, 2023a](https://arxiv.org/abs/2302.10778)), that measurement is just one more
physical interaction, and that the probabilities of the outcomes are Born's. Now we take
the next step, which is also Barandes'. **Collapse is not a new law, it is a
consequence.** And it has a precise stochastic meaning: measurement creates a **division
event**.

## The model: evolve, measure, evolve

We use the same system and the same pointer as in chapter 9:

- the system starts in configuration $j$ and the pointer at rest (*ready*);
- the system evolves with $U$ and the pointer stays put: $U \otimes \mathbb{1}$;
- an ideal measurement $M$ of the observable with eigenvectors $v_a$ (the columns of $V$);
- the system keeps evolving with $W$ and the pointer, with the outcome already recorded,
  stays put: $W \otimes \mathbb{1}$.

The total evolution of the composite system is **a single unitary**:
$$\Theta = (W\otimes\mathbb{1})\,M\,(U\otimes\mathbb{1}).$$
There is no second law. In Lean, this is `measuredEvolution W M U`.

## The mathematics

**Theorem (collapse).** It is a standard computation in von Neumann's model; the formal
version is ours. The amplitude of "system in $i$, pointer at $a$" is
$$\Theta_{(i,a),(j,\text{ready})} = (W v_a)_i \cdot \langle v_a|U|j\rangle .$$

*Proof.* In chapter 9 we saw that, after $M(U\otimes\mathbb 1)$, the $(k, a)$ component is
$(v_a)_k\,\langle v_a|U|j\rangle$. Since $W\otimes\mathbb 1$ does not touch the pointer,
it only mixes system configurations $k$ with the same $a$:
$$\Theta_{(i,a),(j,\text{ready})} = \sum_k W_{ik}\,(v_a)_k\,\langle v_a|U|j\rangle
= (Wv_a)_i\,\langle v_a|U|j\rangle. \qquad\blacksquare$$

Taking the squared modulus:
$$P(i, a \mid j) = \underbrace{|\langle v_a|U|j\rangle|^2}_{\text{Born for } a}\;\cdot\;
\underbrace{|(W v_a)_i|^2}_{\text{evolve from } v_a}.$$

This is exactly the textbook recipe (von Neumann,
[1932](https://doi.org/10.1515/9781400889921)): outcome $a$ occurs with the Born
probability, and **then** the system evolves *as if* it had collapsed to $v_a$. But here
we do not postulate it: it is an identity about the single unitary evolution of the
composite system. What happens afterwards depends on the past **only through the recorded
outcome** $a$.

**Corollary (measurement erases interference).** Summing over the pointer, the system's
transition matrix is
$$\Gamma_{\text{sys}} = |WV|^2 \cdot |V^\dagger U|^2,$$
where $|A|^2$ is the matrix of squared moduli, entry by entry. Without measurement, by
contrast, it would be
$$|WU|^2 = \big|(WV)(V^\dagger U)\big|^2 .$$
The difference is exactly the interference. The squared modulus of a product has cross
terms between the different paths $a$, and the product of the squared moduli does not.
Measurement turns "adding amplitudes" into "adding probabilities". Moreover, $|WV|^2$ and
$|V^\dagger U|^2$ are both stochastic, because they are unistochastic: the evolution of
the system **factors through the outcome** $a$.

## Collapse as a division event

Now we say it in the language of chapter 4. Take any unitary evolution $U(t)$ with
$U(0) = \mathbb 1$, and measure the **configuration** of the system ($V = \mathbb 1$) at a
time $t_1 > 0$. The composite system evolves as:

- for $t < t_1$: $U(t)\otimes\mathbb 1$;
- for $t \ge t_1$: $\big(U(t)U(t_1)^\dagger\otimes\mathbb 1\big)\,M\,\big(U(t_1)\otimes\mathbb 1\big)$.

That is, after the measurement the system continues with **the same dynamics** as
before. The system's process, summing over the pointer, is a generalized stochastic
process (`GenStochasticProcess.measuredAt`).

**Theorem (collapse as a division event).** The measurement time $t_1$ is a division
event of that process, **whatever** the dynamics $U(t)$. The idea is Barandes'
([2023a](https://arxiv.org/abs/2302.10778)); this formal statement and its proof in Lean
are ours.

*Proof.* By the corollary, with $V = \mathbb 1$, for $t \ge t_1$ we have
$$\Gamma(t) = |U(t)U(t_1)^\dagger|^2 \cdot |U(t_1)|^2,
\qquad \Gamma(t_1) = |\mathbb 1|^2\cdot|U(t_1)|^2 = |U(t_1)|^2.$$
So $\Gamma(t) = \Delta(t)\,\Gamma(t_1)$ with $\Delta(t) = |U(t)U(t_1)^\dagger|^2$, which is
stochastic. $\blacksquare$

### The qubit, again

In chapter 6 we proved that, for the qubit with $H = \sigma_x$, time $\pi/4$ is **not** a
division event. At $\pi/4$ the distribution is completely mixed, but at $\pi/2$ the qubit
has swapped its configurations deterministically, and no stochastic law can recover that
information.

If an apparatus measures the qubit's configuration at $\pi/4$, the story changes (the
example is ours): $\pi/4$ **becomes** a division event
(`Qubit.measuredProcess_isDivisionEvent`). The same unitary dynamics gives a divisible or
an indivisible history depending on whether there is a measurement.

> This is Barandes' reading of collapse
> ([Barandes, 2023a](https://arxiv.org/abs/2302.10778)). Measuring does not change the
> laws. What it does is create a division event: an instant from which we can "restart"
> the process and condition on what happened, with ordinary probabilities.

## Decoherence: nobody has to look

Reread the proof of the division event. At no point did we use that someone **reads** the
pointer. All that mattered is that the pointer became **correlated** with the system's
configuration. So the apparatus is nothing special: any environment that records the
configuration should produce the same thing. That is **decoherence**
([Zeh, 1970](https://doi.org/10.1007/BF00708656);
[Joos and Zeh, 1985](https://doi.org/10.1007/BF01725541);
[Zurek, 2003](https://arxiv.org/abs/quant-ph/0105127)), and now we prove it in general in
this model.

### The model

- An **environment** with any finite configuration space $m$, prepared in $e_0$. It can
  be a photon, an air molecule or an apparatus.
- A **recording** interaction $E$ that leaves the system's configuration untouched and
  writes a "record" $\varphi_k$ into the environment:
  $$E\big(|k\rangle\otimes|e_0\rangle\big) = |k\rangle\otimes|\varphi_k\rangle .$$
  The $\varphi_k$ are unit vectors, but **they need not be orthogonal**. The record can be
  imperfect: a photon bouncing off an atom may carry away only a little information about
  where it was.

**Theorem (existence).** For any family of unit records $\varphi_k$ there is a unitary
interaction $E$ that produces them. The proof is the usual trick. The vectors
$|k\rangle\otimes|\varphi_k\rangle$ are orthonormal even if the $\varphi_k$ are not,
because the system part, $|k\rangle$, already separates different $k$. Then they are
completed to a unitary.

### The decoherence formula

The system evolves with $U$, the environment records it, and then the system evolves with
$W$. Summing over the environment:

**Theorem (decoherence formula).** It is the standard formula of decoherence theory (see
[Schlosshauer, 2007](https://doi.org/10.1007/978-3-540-35775-9)), written for transition
probabilities.
$$\Gamma_{ij} = \sum_{k,l} W_{ik}U_{kj}\;\overline{W_{il}U_{lj}}\;\langle\varphi_l,\varphi_k\rangle .$$

The terms with $k = l$ are classical probabilities: going from $j$ to $k$ and then from
$k$ to $i$. The terms with $k \neq l$ are the interference between the paths through $k$
and through $l$, and each one is **weighted by the overlap of their records**. There are
two extreme cases:

- **Perfect record** ($\varphi_k$ orthonormal): $\langle\varphi_l,\varphi_k\rangle = \delta_{kl}$
  and
  $$\Gamma = |W|^2\cdot|U|^2 .$$
  Interference disappears completely.
- **No record** (all $\varphi_k$ equal): $\langle\varphi_l,\varphi_k\rangle = 1$ and
  $$\Gamma = |WU|^2 ,$$
  the coherent evolution, as if the environment were not there.

Between the two extremes, decoherence switches off interference exactly to the extent
that the environment distinguishes the paths.

**Theorem (decoherence creates division events).** The idea is Barandes'; the formal
statement and its proof in Lean are ours. If an environment records the configuration
perfectly at $t_1$, then $t_1$ is a division event of the system's process, whatever the
dynamics. **Nobody has to read the record.**

The measurement at the beginning of the chapter is the special case in which the
environment is an apparatus.

### The qubit with a partial record

Back to the qubit with $H = \sigma_x$. At $\pi/4$, an environment qubit records its
configuration imperfectly: configuration $0$ leaves the record $(1, 0)$ and configuration
$1$ leaves $(\cos\theta, \sin\theta)$. The overlap is $\cos\theta$. With
$\theta = \pi/2$ the record is perfect, and with $\theta = 0$ there is no record.

**Theorem.** The probability that the qubit has swapped its configuration at $\pi/2$ is
$$P(\text{swap}) = \frac{1 + \cos\theta}{2} .$$

With no record ($\cos\theta = 1$) it is $1$: the deterministic swap of chapter 6. With a
perfect record ($\cos\theta = 0$) it is $1/2$: interference has been erased and what is
left is a coin. In between, the curve is continuous.

**Theorem.** $\pi/4$ is a division event **if and only if** the record is perfect,
$\cos\theta = 0$.

This example and its two theorems are ours. As far as we know, this precise statement
does not appear in the literature.

That a partial record is not enough matters. A division event is not "a little bit" true:
either the dynamics factors or it does not. In the real world records are never perfect,
but they become perfect very quickly: many photons, each with an overlap close to one,
multiply their overlaps, which go to zero exponentially
([Joos and Zeh, 1985](https://doi.org/10.1007/BF01725541)). Barandes, Hasan and Kagan
say explicitly that division events "are often only approximate or effective", valid up
to "some given level of precision" ([Barandes, Hasan and Kagan, 2025](https://arxiv.org/abs/2512.18105), §3.1), but they do not give a measure of that
precision. This project proposes one, in the next section.

## Approximate division events

*The definitions and theorems of this section are original to this project.*

We need a distance between transition matrices. We use the worst case, over the initial
configuration $j$, of the total-variation distance between the columns:
$$d(A, B) = \max_j \tfrac12 \sum_i |A_{ij} - B_{ij}| ,$$
a number between $0$ and $1$ for stochastic matrices. It answers an operational question:
how badly can the prediction $B$ fail, in probability, for the worst initial
configuration?

The **division defect** of a time $t'$ is how well the best stochastic laws from $t'$ can
reproduce the true evolution, in the worst later time:
$$\delta(t') = \sup_{t \geq t'}\ \inf_{\Delta \text{ stochastic}} d\big(\Gamma(t),\ \Delta\,\Gamma(t')\big).$$

**Theorem.** For $t' \geq 0$, $\delta(t') = 0$ if and only if $t'$ is a division event.

*Proof.* If $t'$ is a division event, the witnesses $\Delta(t)$ give distance $0$. Conversely,
the stochastic matrices form a compact set (entries in $[0,1]$, closed conditions), and
$\Delta \mapsto d(\Gamma(t), \Delta\Gamma(t'))$ is continuous, so the infimum is attained. If
it is $0$, the minimizer is an exact witness. $\blacksquare$

The compactness matters: without it, a sequence of better and better laws could fail to
have a limit that is a law. We did not find this fact in Mathlib, so we proved it
(`isCompact_colStochastic`).

**Theorem (approximate decoherence).** Suppose the environment records the configuration at
$t_1$, and the records of distinct configurations overlap by at most $\varepsilon$:
$|\langle\phi_l, \phi_k\rangle| \leq \varepsilon$ for $k \neq l$. Then
$$\delta(t_1) \leq \frac{(N-1)\,\varepsilon}{2},$$
where $N$ is the number of configurations.

*Proof idea.* Take as law the fully decohered one, $\Delta = |W|^2$. By the decoherence
formula, the error in the entry $(i,j)$ is the sum of the interference terms $k \neq l$,
each weighted by an overlap of size at most $\varepsilon$. So it is at most
$\varepsilon \sum_{k\neq l} a_k a_l$, with $a_k = |W_{ik}|\,|U_{kj}|$. Summing over $i$,
the Cauchy–Schwarz inequality bounds $\sum_i (\sum_k a_k)^2$ by $N$, and the diagonal terms
$\sum_i \sum_k a_k^2$ add up to exactly $1$. What is left is $N - 1$. $\blacksquare$

For the qubit the bound is **attained**. With the records above, $\varepsilon = |\cos\theta|$,
and we compute exactly
$$\delta(\pi/4) = \frac{|\cos\theta|}{2}.$$
The upper bound uses $\Delta = \mathbb 1$. For the lower bound: $\Gamma(\pi/4)$ has equal
columns, so $\Delta\,\Gamma(\pi/4)$ also does, whatever $\Delta$ is. At $\pi/2$ the two
columns of $\Gamma$ are at total-variation distance $|\cos\theta|$, and a single column
cannot be closer than half that to both.

This makes the earlier "if and only if" quantitative. The defect is not $0$ for a partial
record, but it is proportional to the overlap. With $M$ photons, each with overlap
$\lambda$, the total overlap is $\lambda^M$ and the defect is at most
$(N-1)|\lambda|^M/2$: it goes to zero exponentially, which is Joos and Zeh's argument
turned into a theorem about division events.

In Lean (`Stochastic/ApproxDivision.lean`, `Quantum/Decoherence.lean`,
`Examples/DecoheredQubit.lean`):

```lean
noncomputable def colTV (A B : Matrix n n ℝ) : ℝ := ⨆ j, (∑ i, |A i j - B i j|) / 2

noncomputable def divisionDefect (t' : ℝ) : ℝ :=
  ⨆ t : Set.Ici t', P.factorDefect t' t

theorem isDivisionEvent_iff_divisionDefect_eq_zero {t' : ℝ} (ht' : 0 ≤ t') :
    P.IsDivisionEvent t' ↔ P.divisionDefect t' = 0

theorem recordedAt_divisionDefect_le [Nonempty n] (hEφ : IsRecording φ E e₀)
    (hunit : ∀ j, ∑ e, ‖φ j e‖ ^ 2 = 1) (hε0 : 0 ≤ ε)
    (hε : ∀ k l, k ≠ l → ‖overlap φ k l‖ ≤ ε) :
    (recordedAt U hU h0 E hE e₀ t₁ ht₁).divisionDefect t₁ ≤ (Fintype.card n - 1) * ε / 2

theorem decoheredProcess_divisionDefect (θ : ℝ) :
    (decoheredProcess θ).divisionDefect (Real.pi / 4) = |Real.cos θ| / 2
```

`⨆` and `⨅` are Mathlib's supremum and infimum. Over ℝ they need a bound to behave well,
which is why the proofs carry facts like "the defect is at most $1$". The choice of
distance is ours, and other choices are possible: it is listed as an interpretive choice in
`TRUSTED.md`. How this measure relates to the discrepancy term `qCor` of Barandes, Hasan and
Kagan, and to the divisibility measure of
[Rivas, Huelga and Plenio, 2010](https://doi.org/10.1103/PhysRevLett.105.050403), is still
open.

## What is still missing

- **Arbitrary observables.** The division-event theorem holds for measurements of the
  configuration ($V = \mathbb 1$). For general $V$,
  $\Gamma_{\text{sys}}(t_1) = |V|^2|V^\dagger U|^2$ and the factorization is not
  immediate. The natural statement is about the composite system + pointer process.
- **Repeated measurements** and the quantum Zeno effect.
- **Continuous decoherence.** Records that build up over time. The bound above handles a
  record made at one instant; for $M$ photons it still has to be formalized that the
  overlaps multiply.

## In Lean

```lean
def measuredEvolution (W : Matrix n n ℂ) (M : Matrix (n × Option n) (n × Option n) ℂ)
    (U : Matrix n n ℂ) : Matrix (n × Option n) (n × Option n) ℂ :=
  (W ⊗ₖ (1 : Matrix (Option n) (Option n) ℂ)) *
    (M * (U ⊗ₖ (1 : Matrix (Option n) (Option n) ℂ)))

theorem IsIdealMeasurement.collapse_apply (hM : IsIdealMeasurement V M) (i j a : n) :
    measuredEvolution W M U (i, some a) (j, none) = (W * V) i a * (Vᴴ * U) a j

theorem IsIdealMeasurement.pointerMarginal_measuredEvolution (hM : IsIdealMeasurement V M) :
    pointerMarginal (measuredEvolution W M U) =
      normSqMatrix (W * V) * normSqMatrix (Vᴴ * U)

theorem GenStochasticProcess.measuredAt_isDivisionEvent (hMV : IsIdealMeasurement 1 M) :
    (measuredAt U hU h0 M hM t₁ ht₁).IsDivisionEvent t₁
```

```lean
def IsRecording (φ : n → m → ℂ) (E : Matrix (n × m) (n × m) ℂ) (e₀ : m) : Prop :=
  E ∈ unitaryGroup (n × m) ℂ ∧ ∀ i e j, E (i, e) (j, e₀) = if i = j then φ j e else 0

theorem IsRecording.envMarginal_recordedEvolution (hE : IsRecording φ E e₀)
    (W U : Matrix n n ℂ) (i j : n) :
    (envMarginal (recordedEvolution W E U) e₀ i j : ℂ) =
      ∑ k, ∑ l, W i k * U k j * star (W i l * U l j) * overlap φ k l

theorem Qubit.decoheredProcess_isDivisionEvent_iff (θ : ℝ) :
    (decoheredProcess θ).IsDivisionEvent (Real.pi / 4) ↔ Real.cos θ = 0
```

`(W * V) i a` is $(W v_a)_i$ and `(Vᴴ * U) a j` is $\langle v_a|U|j\rangle$. Note that
`collapse_apply` does not even need $V$ to be unitary: it is pure algebra. Unitarity only
enters when we want the probabilities to sum to one.

## Exercises

1. (Paper) For the qubit measured at $\pi/4$, compute $\Gamma(\pi/2)$ and compare it with
   that of the unmeasured qubit. What information was lost?
2. (Paper) Show with a $2\times 2$ example that $|AB|^2 \neq |A|^2|B|^2$ in general, and
   identify the interference term.
3. (To think about) In the model, the pointer stays put after the measurement. What would
   happen to the division event if the pointer evolved as well?
4. (Paper) Using the decoherence formula, compute $P(\text{swap})$ for the qubit with a
   record of complex overlap $\lambda$. Which part of $\lambda$ matters?
5. (To think about) $N$ photons, each with overlap $\lambda$, leave a total record with
   overlap $\lambda^N$. How many photons are needed for $P(\text{swap})$ to differ from
   $1/2$ by less than $10^{-6}$ if $\lambda = 0.99$?
6. (Lean, open) Prove that measuring the qubit twice, at $t_1 < t_2$, creates two division
   events.
7. (Paper) With $\lambda = 0.99$ per photon and $N = 2$, how many photons make the
   division defect smaller than $10^{-6}$? Compare with exercise 5.
8. (Paper) Show that $d$ is a metric on stochastic matrices and that $d(A, B) \leq 1$.
