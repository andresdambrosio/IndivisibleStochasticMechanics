# 11. Composite systems and entanglement

> Code: `IndivisibleStochasticMechanics/Quantum/Composite.lean`,
> `IndivisibleStochasticMechanics/Quantum/Bell.lean`,
> `IndivisibleStochasticMechanics/Examples/BellPair.lean` and
> `IndivisibleStochasticMechanics/ForMathlib/Matrix/Stochastic.lean`

## The physical idea

Two systems, with configuration spaces $\mathcal{C}_1$ and $\mathcal{C}_2$, form a
composite system whose configurations are **pairs** $(i_1, i_2)$. Nothing more is needed:
in indivisible stochastic mechanics, a composite system is simply a system whose
configuration space is a Cartesian product. Barandes treats composite systems and
entanglement in [Barandes, 2023a, §3.9](https://arxiv.org/abs/2302.10778).

In textbook quantum mechanics, **entanglement** is the most mysterious feature of
composite systems. Einstein, Podolsky and Rosen pointed it out
([1935](https://doi.org/10.1103/PhysRev.47.777)), and Schrödinger named it
(*Verschränkung*) the same year ([Schrödinger, 1935](https://doi.org/10.1007/BF01491891)).
In this chapter we see three things in stochastic language: what happens when the systems
do not interact, why what one of them does cannot be seen in the other's statistics, and
how entanglement shows up in a concrete example. At the end we verify Bell's theorem in
its CHSH form and Tsirelson's bound.

## Independent systems

If the two systems never interact, each evolves with its own unitary and the composite
evolves with the Kronecker product $U(t)\otimes V(t)$. Since
$$|(A\otimes B)_{(i_1,i_2),(j_1,j_2)}|^2 = |A_{i_1j_1}|^2\,|B_{i_2j_2}|^2 ,$$
the Born rule gives

**Theorem (independent systems).** The composite process is the Kronecker product of the
processes:
$$\Gamma(t) = \Gamma_1(t)\otimes\Gamma_2(t).$$

For this to make sense we need a lemma of linear algebra: **the Kronecker product of two
stochastic matrices is stochastic**. Column $(j_1, j_2)$ sums to
$\sum_{i_1}\Gamma^{(1)}_{i_1j_1}\cdot\sum_{i_2}\Gamma^{(2)}_{i_2j_2} = 1\cdot 1$. The lemma
is general and was not in Mathlib, so we put it in `ForMathlib/`.

**Theorem.** If $t'$ is a division event of both processes, it is also one of the product.
*Proof:* if $\Gamma_1(t) = \Delta_1(t)\Gamma_1(t')$ and $\Gamma_2(t) = \Delta_2(t)\Gamma_2(t')$,
the property $(A B)\otimes(C D) = (A\otimes C)(B\otimes D)$ gives
$\Gamma(t) = \big(\Delta_1(t)\otimes\Delta_2(t)\big)\,\Gamma(t')$. $\blacksquare$

These results are standard; the formal statements are ours.

## No signalling

Now the systems may have interacted: the joint evolution $\Theta$ is anything at all.
Alice has system 1 and Bob has system 2. Bob applies a unitary operation $B$ to his system
only. Can Alice notice?

**Theorem (no signalling).** For any joint evolution $\Theta$ and any unitary $B$ on
system 2, the transition probabilities of system 1 do not change:
$$\sum_{i_2}\Big|\big((\mathbb 1\otimes B)\,\Theta\big)_{(i_1,i_2),(j_1,j_2)}\Big|^2
= \sum_{i_2}\big|\Theta_{(i_1,i_2),(j_1,j_2)}\big|^2 .$$

*Proof.* For fixed $i_1$, $j_1$ and $j_2$, the left-hand side is the squared norm of the
vector $B x$, with $x_{i_2} = \Theta_{(i_1,i_2),(j_1,j_2)}$. A unitary preserves the norm.
$\blacksquare$

This is the stochastic version of the no-signalling theorem of quantum mechanics
([Ghirardi, Rimini and Weber, 1980](https://doi.org/10.1007/BF02817189)): what Bob does
does not show up in Alice's statistics, so it cannot be used to send messages. Barandes
discusses the causal locality of his formulation in
[Barandes, 2024](https://arxiv.org/abs/2402.16935).

**Theorem (no signalling for any local operation).** Now Bob does anything at all to his
side: he brings his own ancilla $E$ (for example the pointer of an apparatus) in a state
$e_0$, and applies any unitary $N$ to his system together with $E$. Alice's transition
probabilities do not change:
$$\sum_{i_2,\,e}\Big|\big(N_{\text{Bob}}\,(\Theta\otimes\mathbb 1)\big)_{((i_1,i_2),e),\,(j,e_0)}\Big|^2
= \sum_{i_2}\big|\Theta_{(i_1,i_2),j}\big|^2 .$$
*Proof:* for fixed $i_1$ and $j$, the left-hand side is the squared norm of $N x$ with
$x_{(i_2,e)} = \Theta_{(i_1,i_2),j}\,\delta_{e,e_0}$, and $N$ preserves the norm.
$\blacksquare$ In particular, **Bob measuring his system with his own apparatus** (ideal as
in chapter 9, or not) cannot be seen in Alice's statistics. Every local quantum operation
can be written this way, with an ancilla (Stinespring's theorem, see chapter 8 and the [references](99-references.md)), so this covers
all of them. The formal statement is ours; the result is Ghirardi, Rimini and Weber's.

## Entanglement: a Bell pair

Two qubits start in the configuration $(0,0)$. A Hadamard gate
$H = \tfrac{1}{\sqrt 2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ on the first one and a CNOT
($|a,b\rangle\mapsto|a, b\oplus a\rangle$) prepare the Bell state
$$\frac{|00\rangle + |11\rangle}{\sqrt 2}$$
(see for example [Nielsen and Chuang, 2000, §1.3.6](https://doi.org/10.1017/CBO9780511976667)).
This example and its four theorems in stochastic language are ours. The quantum facts
they use are textbook material.

**Theorem (correlation).** Right after the preparation, the two qubits agree: the
configuration is $(0,0)$ or $(1,1)$, each with probability $1/2$. This distribution **is
not a product** $p\otimes q$.

*Proof of the second part.* If it were, then $p_0 q_0 = 1/2$, $p_1 q_1 = 1/2$ and
$p_0 q_1 = 0$. But $p_0 q_1 = 0$ means $p_0 = 0$ or $q_1 = 0$, and either one contradicts
one of the other equalities. $\blacksquare$

So far there is nothing quantum: two coins that someone glued together also always agree.
The difference shows up when we change basis.

**Theorem (without a division event).** If after the preparation we apply a Hadamard to
**each** qubit, the qubits *still* agree with certainty: $(0,0)$ or $(1,1)$, each with
probability $1/2$. That is because the Bell state is invariant under $H\otimes H$.

**Theorem (with a division event).** If right after the preparation an environment
**records** the configuration of the two qubits (a perfect record, as in chapter 10), the
same local Hadamards give the **uniform** distribution: each of the four configurations
with probability $1/4$. Nobody has to read the record.

At the intermediate time, the two histories have **exactly the same** configuration
statistics: $(0,0)$ or $(1,1)$ with probability $1/2$. What tells them apart is whether
that time is a division event.

> In the language of this book, the entanglement of the Bell pair looks like this:
> **correlations plus the absence of a division event**. The glued coins are correlations
> *with* a division event. This is our way of summarizing the example; for Barandes'
> general discussion see [Barandes, 2023a, §3.9](https://arxiv.org/abs/2302.10778).

## Bell nonlocality: CHSH and Tsirelson

The Bell pair also lets us check, in Lean, the most famous theorem about entanglement.
Alice chooses one of two settings $x\in\{0,1\}$ and Bob one of two settings $y\in\{0,1\}$.
Each one gets an outcome $\pm1$, and $E(x,y)$ is the average of the product of the
outcomes. The **CHSH combination** is
$$S = E(0,0) + E(0,1) + E(1,0) - E(1,1).$$

**Theorem (CHSH inequality).** In every local hidden-variable model, $|S|\le 2$.

A *local hidden-variable model* is the kind of theory Bell considered
([Bell, 1964](https://doi.org/10.1103/PhysicsPhysiqueFizika.1.195)): a hidden variable
$\lambda$ is drawn with some distribution, and Alice's outcome depends only on $\lambda$ and
on her setting, not on Bob's (and vice versa). The inequality is the one of
[Clauser, Horne, Shimony and Holt, 1969](https://doi.org/10.1103/PhysRevLett.23.880).
*Proof:* for each $\lambda$, with $a_x, b_y\in[-1,1]$,
$a_0(b_0+b_1) + a_1(b_0-b_1)$ has absolute value at most $|b_0+b_1| + |b_0-b_1| \le 2$;
averaging over $\lambda$ keeps the bound. $\blacksquare$ In Lean we take $\lambda$ in a finite
set and outcomes in $[-1,1]$, which also covers local randomness.

**Theorem (the Bell pair, stochastically).** Alice rotates her qubit by an angle $a$ and Bob
rotates his by $b$ (local unitaries), and then both configurations are read. With outcome
$+1$ for configuration $0$ and $-1$ for $1$, the transition probabilities of the composite
process give
$$E(a,b) = \cos 2(a-b).$$
With the standard settings $a\in\{0,\pi/4\}$ and $b\in\{\pi/8,-\pi/8\}$,
$$S = 2\sqrt2 \approx 2.83 > 2.$$
So **no local hidden-variable model reproduces these transition probabilities.** The
calculation is textbook quantum mechanics; stating it for the transition probabilities of
the composite process is ours.

**Theorem (Tsirelson's bound).** For any state $\psi$ and any observables
$A_0, A_1, B_0, B_1$ with eigenvalues $\pm1$, where Alice's commute with Bob's,
$$\langle\psi, (A_0B_0 + A_0B_1 + A_1B_0 - A_1B_1)\,\psi\rangle \le 2\sqrt2\,\|\psi\|^2 .$$
This is the result of [Cirel'son, 1980](https://doi.org/10.1007/BF00417500). *Proof* (the
standard sum-of-squares argument): with $s = \sqrt2$,
$$(sA_0 - B_0 - B_1)^2 + (sA_1 - B_0 + B_1)^2 = 8 - 2s\,(A_0B_0 + A_0B_1 + A_1B_0 - A_1B_1),$$
and the left-hand side has a non-negative expectation. $\blacksquare$ So the Bell pair is
optimal: quantum mechanics goes beyond 2, but never beyond $2\sqrt2$.

**Theorem (Tsirelson, stochastically).** The same bound holds directly for the transition
probabilities of a composite process. Take any unitary preparation $\Theta$ of the two
systems, any local unitaries $U_x$ for Alice and $V_y$ for Bob, and any assignment of
outcomes $\pm1$ to configurations. Then the correlations
$$E(x,y) = \sum_{i_1,i_2} a_x(i_1)\,b_y(i_2)\;\Gamma^{xy}_{(i_1,i_2),\,j}$$
computed from the transition matrices $\Gamma^{xy}$ satisfy $|S| \le 2\sqrt2$. *Proof:*
$E(x,y)$ is the quantum expectation value of $(U_x^\dagger D_{a_x} U_x)\otimes(V_y^\dagger
D_{b_y} V_y)$ in the state $\Theta e_j$, where $D_a$ is the diagonal matrix of outcomes.
These observables square to $1$, so the previous theorem applies. $\blacksquare$ The bound
is Cirel'son's; stating it for transition probabilities is ours.

**Theorem (with apparatuses).** So far, "measuring" meant rotating and then reading the
configuration. Now each side measures with an ideal apparatus as in chapter 9: Alice with an
apparatus for the basis $V_x$ and her own pointer, Bob with one for $W_y$ and his own
pointer. Each apparatus acts only on its own system and pointer. Then the pointers read
$(a,b)$ with probability
$$P(a,b) = \Big|\big((V_x^\dagger\otimes W_y^\dagger)\,\Theta\big)_{(a,b),\,j}\Big|^2 ,$$
exactly the probability of "rotate by $V_x^\dagger$, $W_y^\dagger$ and read". As a
consequence, **the pointers also satisfy $|S|\le 2\sqrt2$**, and for the Bell pair, with
apparatuses for the rotated bases, **the pointers reach $S = 2\sqrt2$**. The physics is
standard measurement theory; these three statements in this form, and their formal proofs,
are ours.

What does this mean for indivisible stochastic mechanics? The configurations are real at
every time, but they are **not** a local hidden variable in Bell's sense: the theorem shows
that no such variable reproduces the statistics. In the language of this book, the reason
is the one we already saw: the time right after the preparation is not a division event,
so the configuration at that time does not "screen off" the future. This reading is ours;
for how locality fits into Barandes' formulation, see
[Barandes, 2024](https://arxiv.org/abs/2402.16935).

## What is still missing

- **Non-ideal measurements.** The apparatuses here are ideal (projective). General
  measurements (POVMs) are pending.
- **The locality question.** Barandes argues that his formulation is causally local
  ([Barandes, 2024](https://arxiv.org/abs/2402.16935)). Formalizing that claim is a
  stage III task on the roadmap.

## In Lean

```lean
theorem Matrix.kronecker_mem_colStochastic (hA : A ∈ colStochastic R m)
    (hB : B ∈ colStochastic R n) : A ⊗ₖ B ∈ colStochastic R (m × n)

def GenStochasticProcess.prod (P : GenStochasticProcess n) (Q : GenStochasticProcess m) :
    GenStochasticProcess (n × m) where
  Γ t := P.Γ t ⊗ₖ Q.Γ t
  ...

theorem GenStochasticProcess.prod_isDivisionEvent (hP : P.IsDivisionEvent t')
    (hQ : Q.IsDivisionEvent t') : (P.prod Q).IsDivisionEvent t'

theorem envMarginal_one_kronecker_mul (hB : B ∈ unitaryGroup m ℂ)
    (Θ : Matrix (n × m) (n × m) ℂ) (e₀ : m) :
    envMarginal (((1 : Matrix n n ℂ) ⊗ₖ B) * Θ) e₀ = envMarginal Θ e₀
```

`envMarginal Θ e₀` is the transition matrix of system 1 summing over system 2, with
system 2 starting in $e_0$: the same one we used for the environment in chapter 10. Here
the "environment" is Bob's system.

```lean
theorem BellPair.not_product :
    ¬ ∃ p q : Fin 2 → ℝ, ∀ i, normSqMatrix prep i (0, 0) = p i.1 * q i.2

theorem BellPair.coherent (i : Fin 2 × Fin 2) :
    normSqMatrix ((hadamard ⊗ₖ hadamard) * prep) i (0, 0) = if i.1 = i.2 then 1 / 2 else 0

theorem BellPair.decohered_of_isRecording (hE : IsRecording φ E e₀)
    (hφ : ∀ k l, overlap φ k l = if k = l then 1 else 0) (i : Fin 2 × Fin 2) :
    envMarginal (recordedEvolution (hadamard ⊗ₖ hadamard) E prep) e₀ i (0, 0) = 1 / 4
```

```lean
theorem LHVModel.abs_chsh_corr_le_two (L : LHVModel Λ) : |chsh L.corr| ≤ 2

theorem BellPair.corr_eq (a b : ℝ) : corr a b = Real.cos (2 * (a - b))
theorem BellPair.chsh_bellCorr : chsh bellCorr = 2 * Real.sqrt 2
theorem BellPair.lhv_corr_ne_bellCorr (L : LHVModel Λ) : L.corr ≠ bellCorr

theorem expect_chsh_le ... (ψ : ι → ℂ) :
    expect (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) ψ ≤ 2 * Real.sqrt 2 * ∑ i, ‖ψ i‖ ^ 2

theorem abs_chsh_stochCorr_le (hΘ : Θ ∈ unitaryGroup (A × B) ℂ) (hU : ∀ x, U x ∈ ...)
    (hV : ∀ y, V y ∈ ...) (ha : ∀ x i, a x i = 1 ∨ a x i = -1) (hb : ...) (j : A × B) :
    |chsh (stochCorr Θ U V a b j)| ≤ 2 * Real.sqrt 2

theorem pointerJoint_eq (hM : IsIdealMeasurement V M) (hN : IsIdealMeasurement W N)
    (hV : V ∈ unitaryGroup A ℂ) (hW : W ∈ unitaryGroup B ℂ) (Θ) (j) (a) (b) :
    pointerJoint M N Θ j a b = normSqMatrix ((Vᴴ ⊗ₖ Wᴴ) * Θ) (a, b) j

theorem BellPair.chsh_pointerCorr (hM : ∀ x, IsIdealMeasurement (rot (alice x))ᴴ (M x))
    (hN : ∀ y, IsIdealMeasurement (rot (bob y))ᴴ (N y)) :
    chsh (pointerCorr M N prep (fun _ => sgn) (fun _ => sgn) (0, 0)) = 2 * Real.sqrt 2
```

## Exercises

1. (Paper) Check by hand that $(H\otimes H)\,\tfrac{1}{\sqrt2}(|00\rangle+|11\rangle) =
   \tfrac{1}{\sqrt2}(|00\rangle+|11\rangle)$.
2. (Paper) In the Bell pair, what is the distribution of the configurations of Alice's
   qubit alone? Does it change if Bob applies a Hadamard? Compare with the no-signalling
   theorem.
3. (Paper) Repeat the example with the state $\tfrac{1}{\sqrt2}(|01\rangle-|10\rangle)$.
   Which local gates leave the correlations intact?
4. (To think about) The "glued coins" and the Bell pair have the same distribution at the
   intermediate time. Is there any way to tell them apart by looking at that time alone?
5. (Paper) Check that $S = 2\sqrt2$ from $E(a,b) = \cos 2(a-b)$ and the four angles.
6. (Paper) Why does the no-signalling proof need Bob's ancilla to be his alone? What goes
   wrong if the ancilla is shared with Alice?
