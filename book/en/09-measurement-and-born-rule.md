# 9. Measurement and the Born rule

> Code: `IndivisibleStochasticMechanics/Quantum/Measurement.lean`

## The problem

The Born rule is the heart of textbook quantum mechanics. If we measure an observable with
orthonormal eigenvectors $\{v_a\}$ on a state $\psi$, we get outcome $a$ with probability
$$P(a) = |\langle v_a, \psi\rangle|^2 .$$
But in the usual formulation this is a **postulate**, and moreover it invokes a primitive
notion of "measurement" that the theory never defines. That is the measurement problem.

In the previous chapters we only obtained probabilities of **configurations**, that is,
of the observables that are diagonal in the configuration basis. What about the rest?
What happens if we measure something whose eigenvectors are not configurations, like
$\sigma_x$ on a qubit whose configurations are the eigenstates of $\sigma_z$?

## The stochastic answer

The argument of this section is Barandes'
([Barandes, 2023a](https://arxiv.org/abs/2302.10778)). The measurement model is von
Neumann's ([1932, ch. VI](https://doi.org/10.1515/9781400889921)).

In indivisible stochastic mechanics **only configurations are physical**. A measurement is
not a special operation: it is a **physical interaction** between the system and an
apparatus. The apparatus also has configurations, because the needle of an instrument is
somewhere. The outcome of the measurement *is* the configuration of the pointer.

Therefore the probability of an outcome is the probability of a configuration of the
composite system (system + apparatus). That is an ordinary transition probability of the
composite stochastic process. No new postulate is needed.

What has to be proved is that **these probabilities coincide with Born's**.

## The model

- **System:** configurations $j \in \mathcal{C}$.
- **Pointer:** a rest configuration, *ready*, and one configuration $a$ for each possible
  outcome. In Lean it is `Option n`: `none` is *ready* and `some a` shows $a$.
- **Observable:** its eigenvectors $v_a$ are the columns of a unitary matrix $V$. We write
  $P_a = |v_a\rangle\langle v_a|$ for the projector onto each one.

**Definition (ideal von Neumann measurement).** A unitary $M$ on system ⊗ pointer that,
with the pointer at rest, acts as
$$M\big(|j\rangle \otimes |\text{ready}\rangle\big) = \sum_a P_a|j\rangle \otimes |a\rangle .$$
In words: the pointer comes to show $a$, correlated with the component of the system
along $v_a$.

## The mathematics

**Theorem (existence).** Every observable, given by an orthonormal basis of eigenvectors,
has an ideal measurement interaction.

*Proof.* It is the same trick as in chapter 8. The vectors
$c_j = \sum_a P_a|j\rangle\otimes|a\rangle$ are orthonormal:
$$\langle c_j, c_k\rangle = \sum_a \langle j|P_a P_a|k\rangle = \sum_a \langle j|P_a|k\rangle = \langle j|k\rangle = \delta_{jk},$$
because the $P_a$ are projectors that sum to the identity. Then they are completed to a
unitary with the `ForMathlib` lemma. $\blacksquare$

**Theorem (Born rule from configurations).** If the system is in state $\psi$ and the
pointer at rest, after the ideal measurement the probability that the pointer shows $a$ is
$$\sum_i \big|\big(M(\psi\otimes|\text{ready}\rangle)\big)_{(i,a)}\big|^2 = |\langle v_a, \psi\rangle|^2 .$$

*Proof.* The $(i, a)$ component of the final state is
$(P_a\psi)_i = (v_a)_i\,\langle v_a,\psi\rangle$. Summing over the system's
configurations $i$:
$$\sum_i |(v_a)_i|^2\,|\langle v_a,\psi\rangle|^2 = |\langle v_a,\psi\rangle|^2,$$
because $v_a$ is normalized. $\blacksquare$

**Corollary (the Born rule in stochastic language).** Suppose the system starts in
configuration $j$, evolves with $U$, and is then measured. The probability that the
pointer ends in configuration $a$ is
$$|\langle v_a|U|j\rangle|^2 .$$
This number is a **transition probability of the composite stochastic process**, whose
evolution is the unitary $M\,(U\otimes\mathbb{1})$, summed over the final configuration of
the system.

## What we gain

The argument is Barandes', and the measurement model is von Neumann's. What this chapter
contributes is the formal version, verified in Lean. Before, the Born rule for arbitrary
observables was a postulate. Now it is a theorem that says the following: **if the
apparatus is one more physical system and the outcomes are its configurations, the
probabilities of the outcomes are Born's**. We used only two things: the rule for
configurations, which in this theory is the definition of the transition probabilities,
and the physics of the interaction.

## What is still missing

This is the first step, not the complete argument. It is recorded in `TRUSTED.md` and on
the roadmap.

- **Degenerate observables:** here each outcome has a single eigenvector. The general
  case requires projectors of higher rank.
- **Non-ideal measurements and POVMs:** noisy or imperfect apparatuses.
- **"Collapse":** we want to prove that after the measurement there is a **division
  event**. The composite system "restarts" and later evolution depends only on the
  recorded outcome. In this theory, collapse is nothing but conditioning ordinary
  probabilities on a division event. We prove it in
  [chapter 10](10-collapse-and-decoherence.md).

## In Lean

```lean
def IsIdealMeasurement (V : Matrix n n ℂ) (M : Matrix (n × Option n) (n × Option n) ℂ) :
    Prop :=
  M ∈ unitaryGroup (n × Option n) ℂ ∧
    ∀ i j, M (i, none) (j, none) = 0 ∧ ∀ a, M (i, some a) (j, none) = V i a * star (V j a)
```

The entry $(i, a), (j, \text{ready})$ is $V_{ia}\overline{V_{ja}} = (P_a)_{ij}$. The
entries with the pointer at rest at the end are zero: after measuring, the pointer always
shows something.

```lean
theorem IsIdealMeasurement.pointer_prob (hV : V ∈ unitaryGroup n ℂ)
    (hM : IsIdealMeasurement V M) (ψ : n → ℂ) (a : n) :
    ∑ i, ‖(M *ᵥ readyState ψ) (i, some a)‖ ^ 2 = ‖(Vᴴ *ᵥ ψ) a‖ ^ 2

theorem IsIdealMeasurement.prob_after_evolution (hV : V ∈ unitaryGroup n ℂ)
    (hM : IsIdealMeasurement V M) (j a : n) :
    ∑ i, ‖(M * (U ⊗ₖ (1 : Matrix (Option n) (Option n) ℂ))) (i, some a) (j, none)‖ ^ 2 =
      ‖(Vᴴ * U) a j‖ ^ 2
```

`(Vᴴ *ᵥ ψ) a` is $\langle v_a, \psi\rangle$, and `U ⊗ₖ 1` is the Kronecker product
$U \otimes \mathbb{1}$: the system evolves and the pointer stays put.

## Exercises

1. (Paper) Qubit with configurations $|0\rangle, |1\rangle$. Measure $\sigma_x$, whose
   eigenvectors are $|\pm\rangle = (|0\rangle \pm |1\rangle)/\sqrt2$, on the state
   $|0\rangle$. Write $V$ and the column of $M$ corresponding to
   $|0\rangle\otimes|\text{ready}\rangle$, and check that the pointer shows each outcome
   with probability $1/2$.
2. (Paper) In the previous exercise, which columns of $M$ remain free? Do they affect any
   physical result?
3. (To think about) The theorem never uses that $M$ is unitary, except so that it exists
   as a physical evolution. Why does it still matter to require it?
4. (Lean, open) Extend `IsIdealMeasurement` to degenerate observables.
