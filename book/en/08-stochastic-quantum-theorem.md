# 8. The stochastic-quantum theorem: from processes to Hilbert spaces

> Code: `IndivisibleStochasticMechanics/Quantum/Dilation.lean`,
> `IndivisibleStochasticMechanics/ForMathlib/Matrix/Unitary.lean`

In chapter 5 we saw one direction of the correspondence: every unitary evolution defines a
stochastic process. This chapter proves the other: **every stochastic process can be seen
as a quantum system**. The theorem is Barandes'
([Barandes, 2023b](https://arxiv.org/abs/2309.03085)). With both directions together we
get the project's first verified equivalence theorem.

## The obstacle

The most direct approach would be to look, for each stochastic $\Gamma$, for a unitary $U$
with $\Gamma_{ij} = |U_{ij}|^2$. But in chapter 5 we saw that it **does not always
exist**: the matrix
$$\tfrac{1}{2}\begin{pmatrix}1&1&0\\0&1&1\\1&0&1\end{pmatrix}$$
is stochastic and not unistochastic. On the same configuration space there is no unitary
evolution that produces it.

## The way out: enlarge the system

The idea, central in quantum mechanics, is that a system that does not evolve unitarily
can be **part** of a larger system that does. We add an **environment** with
configurations $e \in \mathcal{E}$, prepared in a fixed state $e_0$, and require

$$\Gamma_{ij} = \sum_{e \in \mathcal{E}} \big|U_{(i,e),(j,e_0)}\big|^2 .$$

In words: $\Gamma_{ij}$ is the probability of finding the **system** in $i$, *whatever the
environment does*, if it started in $j$ and the environment in $e_0$. This is called a
**unitary dilation** of $\Gamma$. It is the same idea as Stinespring's dilation theorem
([Stinespring, 1955](https://doi.org/10.2307/2032342)).

## The mathematics

**Definition.** $U$ is a unitary dilation of $\Gamma$, with environment $\mathcal{E}$ and
initial state $e_0$, if $U$ is unitary on $\mathcal{C}\times\mathcal{E}$ and
$\Gamma_{ij} = \sum_e |U_{(i,e),(j,e_0)}|^2$ for all $i, j$.

**Proposition (from quantum to stochastic).** If $U$ is a unitary dilation of $\Gamma$,
then $\Gamma$ is stochastic.

*Proof.* The entries are sums of squared moduli, so they are $\ge 0$. Column $j$ sums to
$$\sum_i \Gamma_{ij} = \sum_i\sum_e |U_{(i,e),(j,e_0)}|^2 = \sum_{(i,e)} |U_{(i,e),(j,e_0)}|^2 = 1,$$
because it is the squared norm of column $(j,e_0)$ of a unitary matrix. $\blacksquare$

**Theorem (from stochastic to quantum).** Every stochastic matrix $\Gamma$ has a unitary
dilation. An environment with $N+1$ configurations suffices.

*Proof.* This concrete construction is ours. It is a direct dilation of Stinespring type,
and it need not coincide with Barandes', who goes through Kraus operators and a
Stinespring dilation of dimension at most $N^3$
([Barandes, 2026](https://arxiv.org/abs/2602.01043), §5); ours has dimension $N(N+1)$. Take as environment
$\mathcal{E} = \{\varnothing\} \cup \mathcal{C}$, with initial state
$e_0 = \varnothing$. In Lean this is `Option n`, and $\varnothing$ is `none`. For each
initial configuration $j$, define the vector
$$v_j = \sum_i \sqrt{\Gamma_{ij}}\; |i\rangle \otimes |j\rangle_{\mathcal{E}} .$$
Physically: the system goes to $i$ with amplitude $\sqrt{\Gamma_{ij}}$, and the
environment **records** where it started.

*Step 1: the $v_j$ are orthonormal.*
$$\langle v_j, v_k\rangle = \sum_i \sqrt{\Gamma_{ij}}\sqrt{\Gamma_{ik}}\;\langle j|k\rangle_{\mathcal{E}} = \delta_{jk}\sum_i \Gamma_{ij} = \delta_{jk}.$$
What is notable is that **the normalization condition of a stochastic matrix (columns
sum to 1) is exactly the normalization of the vectors $v_j$**. And orthogonality comes
from the environment, because it keeps the initial configuration.

*Step 2: complete to a unitary.* An orthonormal family can always be completed to an
orthonormal basis of the whole space. The matrix $U$ whose columns are that basis is
unitary, and its column $(j, \varnothing)$ is $v_j$.

*Step 3: recover $\Gamma$.*
$$\sum_e |U_{(i,e),(j,\varnothing)}|^2 = \sum_e |(v_j)_{(i,e)}|^2 = \big|\sqrt{\Gamma_{ij}}\big|^2 = \Gamma_{ij}. \qquad\blacksquare$$

**Corollary (stochastic-quantum correspondence in finite dimensions).** A family of
matrices $\Gamma(t)$ is stochastic at every $t \ge 0$ **if and only if** at every
$t \ge 0$ it is the marginal of a unitary evolution $U(t)$ of system plus environment.

## What the theorem says and what it does not

This discussion is ours. It is the kind of discussion that formalization forces you to have, and that is why it
is also recorded in `TRUSTED.md`.

- **What it says:** at each instant, the transition probabilities of *any* stochastic
  process are those of a quantum system, provided it is seen as part of a larger system.
- **What it does not say:** $U(t)$ is chosen **separately at each instant**. The theorem
  does not guarantee that $U(t)$ is continuous in $t$, nor that $U(0) = \mathbb{1}$, nor
  that it comes from a Hamiltonian. A stronger version that requires this is the next
  task on the roadmap.
- **Why it is not cheating:** indivisibility means that one cannot simply require
  $U(t) = U(t\leftarrow t')U(t')$. Stochastic laws condition on the initial time, and so
  does the dilation.

## In Lean

The definition:

```lean
def IsUnitaryDilation (Γ : Matrix n n ℝ) (U : Matrix (n × m) (n × m) ℂ) (e₀ : m) : Prop :=
  U ∈ unitaryGroup (n × m) ℂ ∧ ∀ i j, Γ i j = ∑ e, ‖U (i, e) (j, e₀)‖ ^ 2
```

The space of system plus environment is the product `n × m`, and its configurations are
pairs `(i, e)`.

The vectors $v_j$:

```lean
noncomputable def dilationVec (Γ : Matrix n n ℝ) (c : n × Option n) :
    EuclideanSpace ℂ (n × Option n) :=
  WithLp.toLp 2 fun a => if a.2 = some c.1 then (Real.sqrt (Γ a.1 c.1) : ℂ) else 0
```

`EuclideanSpace ℂ ι` is $\mathbb{C}^\iota$ with its inner product, and `WithLp.toLp 2`
turns a function into a vector of that space. The $(i, e)$ entry is $\sqrt{\Gamma_{ij}}$
if the environment recorded $j$ ($e = $ `some j`) and $0$ otherwise.

Step 2 is a general result of linear algebra, so we put it in `ForMathlib/`, the folder
for results meant to be upstreamed to Mathlib:

```lean
theorem exists_mem_unitaryGroup_of_orthonormal {s : Set ι} {v : ι → EuclideanSpace 𝕜 ι}
    (hv : Orthonormal 𝕜 (s.domRestrict v)) :
    ∃ U ∈ unitaryGroup ι 𝕜, ∀ j ∈ s, ∀ i, U i j = v j i
```

The proof uses `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`, which
completes the family to a basis, and `toMatrix_orthonormalBasis_mem_unitary`, which says
that the matrix of an orthonormal basis is unitary. Both were already in Mathlib.

With all that, the main theorem is short:

```lean
theorem forall_mem_colStochastic_iff_exists_isUnitaryDilation (Γ : ℝ → Matrix n n ℝ) :
    (∀ t, 0 ≤ t → Γ t ∈ colStochastic ℝ n) ↔
      ∃ U : ℝ → Matrix (n × Option n) (n × Option n) ℂ,
        ∀ t, 0 ≤ t → IsUnitaryDilation (Γ t) (U t) none
```

In the "⇒" direction, `choose` picks a dilation for each instant: it is the axiom of
choice. In the "⇐" direction, the proposition from quantum to stochastic applies.

To check that there are no hidden tricks, Lean can tell you which axioms a theorem
depends on:

```lean
#print axioms ISM.forall_mem_colStochastic_iff_exists_isUnitaryDilation
-- [propext, Classical.choice, Quot.sound]
```

These are the three standard axioms all of Mathlib rests on. There is no `sorry` and no
additional assumption.

## Exercises

1. (Paper) Explicitly construct the dilation of the non-unistochastic $3\times 3$ matrix
   from the beginning of the chapter. How many columns of $U$ are determined by $\Gamma$
   and how many are free?
2. (Paper) If $\Gamma$ is already unistochastic, with $\Gamma = |V|^2$, show that there is
   a dilation with an environment of a **single** configuration.
3. (Paper) At time $t = 0$, $\Gamma(0) = \mathbb{1}$. What does our construction do with
   the environment at that instant? Why does that prevent $U(0) = \mathbb{1}$? How would
   you fix it?
4. (Lean, open) Strengthen the theorem so that $U(0) = \mathbb{1}$. It is a task on the
   roadmap.
