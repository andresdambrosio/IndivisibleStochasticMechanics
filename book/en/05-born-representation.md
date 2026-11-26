# 5. The Born representation and unitary evolution

> Code: `Stochastic/Unistochastic.lean`, `Quantum/UnitaryProcess.lean`

## The physical idea

How do we connect a stochastic process with quantum mechanics? Through the Born rule. If
the system starts in configuration $j$, its quantum state is the basis vector
$|j\rangle$. After a time $t$ it is $U(t)|j\rangle$, and the probability of finding it in
$i$ is

$$\Gamma_{ij}(t) = |\langle i|U(t)|j\rangle|^2 = |U_{ij}(t)|^2.$$

The formula is the Born rule ([Born, 1926](https://doi.org/10.1007/BF01397477)).
Barandes ([Barandes, 2023a](https://arxiv.org/abs/2302.10778)) turns the usual reading
around. This formula does not describe "what happens upon measurement", but **the
transition probabilities of the underlying stochastic process**.

## The mathematics

**Definition (Born representation, following
[Barandes, 2023b](https://arxiv.org/abs/2309.03085)).** A complex matrix $\Theta$ is a
Born representation of $\Gamma$ if $\Gamma_{ij} = |\Theta_{ij}|^2$ for all $i,j$.

**Definition.** $\Gamma$ is **unistochastic** if it has a *unitary* Born representation.
It is a classic notion of linear algebra (see, for example,
[Życzkowski, Słomczyński, Kuś and Sommers, 2003](https://arxiv.org/abs/nlin/0112036)).

**Lemma.** If $U$ is unitary, its columns are unit vectors: $\sum_i |U_{ij}|^2 = 1$.

*Proof.* $U^\dagger U = \mathbb{1}$. The $(j,j)$ entry is
$\sum_i \overline{U_{ij}}\,U_{ij} = \sum_i |U_{ij}|^2 = 1$. $\blacksquare$

**Corollary.** Every unistochastic matrix is stochastic. The entries are squared moduli,
so they are $\geq 0$, and the lemma says the columns sum to 1.

**Theorem (from quantum to stochastic).** If $U(t)$ is unitary for every $t$ and
$U(0)=\mathbb{1}$, then $\Gamma_{ij}(t) = |U_{ij}(t)|^2$ defines a generalized stochastic
process.

*Proof.* By the corollary, each $\Gamma(t)$ is stochastic. Moreover
$\Gamma_{ij}(0) = |\delta_{ij}|^2 = \delta_{ij}$. $\blacksquare$

**Warning.** Not every stochastic matrix is unistochastic. The classic example is the
$3\times 3$ matrix
$$\tfrac{1}{2}\begin{pmatrix}1&1&0\\0&1&1\\1&0&1\end{pmatrix},$$
which is not. It is a well-known example from the literature on unistochastic matrices,
and exercise 1 asks you to prove it. That is why Barandes' theorem in the reverse
direction needs, in general, a **larger** configuration space. We will see it in
chapter 8.

## In Lean

```lean
def IsBornRep (Γ : Matrix n n ℝ) (Θ : Matrix n n ℂ) : Prop :=
  ∀ i j, Γ i j = ‖Θ i j‖ ^ 2

def IsUnistochastic (Γ : Matrix n n ℝ) : Prop :=
  ∃ U ∈ Matrix.unitaryGroup n ℂ, IsBornRep Γ U
```

`‖z‖` is the modulus of a complex number. The column lemma:

```lean
theorem unitary_col_normSq_sum {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (j : n) : ∑ i, ‖U i j‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU) j) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.star_def,
    Complex.conj_mul'] at h
  exact_mod_cast h
```

Step by step:
1. `mem_unitaryGroup_iff'` turns "$U$ is unitary" into $U^\dagger U = \mathbb{1}$, and
   `congrFun` twice keeps the $(j,j)$ entry.
2. `simp only [...]` expands that entry: the matrix product is a sum,
   $\overline{z}z = |z|^2$ and $\mathbb{1}_{jj} = 1$.
3. What remains is $\sum_i |U_{ij}|^2 = 1$ as an equality *in $\mathbb{C}$*.
   `exact_mod_cast` brings it down to $\mathbb{R}$.

We did this proof in the project. At first it was a `sorry`, left as a *good first
issue*.

The main theorem of the chapter is a **definition** with proofs inside:

```lean
noncomputable def ofUnitary (U : ℝ → Matrix n n ℂ) (hU : ∀ t, U t ∈ Matrix.unitaryGroup n ℂ)
    (h0 : U 0 = 1) : GenStochasticProcess n where
  Γ t := Matrix.of fun i j => ‖U t i j‖ ^ 2
  stochastic t _ := (isUnistochastic_normSq (hU t)).mem_colStochastic
  init := by
    ext i j
    by_cases h : i = j <;> simp [h0, Matrix.one_apply, h]
```

That Lean accepts `ofUnitary` *is* the proof of the theorem: to build a
`GenStochasticProcess` you must prove `stochastic` and `init`. `noncomputable` means that
the modulus of a complex number cannot be "computed" exactly on a computer, which is
irrelevant for proofs.

## Exercises

1. (Paper) Prove that the $3\times 3$ matrix in the warning is not unistochastic. Hint:
   since $U_{21} = 0$ and $U_{32} = 0$, the inner product of columns 1 and 2 of $U$ has a
   single nonvanishing term, and it cannot be zero.
2. (Paper) If $\Theta$ is a Born representation of $\Gamma$ and $D$ is a diagonal matrix
   of phases ($|D_{ii}|=1$), are $D\Theta$ and $\Theta D$ also Born representations? This
   is the **gauge freedom** of the representation.
3. (Lean) Prove that every stochastic matrix has *some* Born representation. Hint:
   $\Theta_{ij} = \sqrt{\Gamma_{ij}}$. It is on the roadmap.
