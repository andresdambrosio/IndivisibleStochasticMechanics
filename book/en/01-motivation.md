# 1. Why reformulate quantum mechanics

## The theory that works and that nobody understands

Quantum mechanics is the most predictively successful physical theory in history. Yet its
textbook formulation, that of Dirac (1930) and von Neumann
([1932](https://doi.org/10.1515/9781400889921)), has an awkward structure:

1. The state of a system is a vector $|\psi\rangle$ in a Hilbert space.
2. While nobody measures, $|\psi\rangle$ evolves deterministically and unitarily:
   $|\psi(t)\rangle = U(t)|\psi(0)\rangle$.
3. When someone *measures*, the state "collapses" at random, with probabilities given by
   the **Born rule** ([Born, 1926](https://doi.org/10.1007/BF01397477)):
   $P(i) = |\langle i|\psi\rangle|^2$.

This structure gives rise to the famous **measurement problem**. What counts as a
measurement? Why are there two different laws of evolution? What *is* $|\psi\rangle$:
something physical, or a record of our knowledge? The various interpretations
(Copenhagen, many worlds, Bohm, objective collapse, QBism...) are different answers to
these questions.

## Barandes' proposal

Barandes ([Barandes, 2023a](https://arxiv.org/abs/2302.10778),
[Barandes, 2025](https://arxiv.org/abs/2507.21192)) proposes to turn the usual order
around. In our words:

> A quantum system **is** a system that, at each instant, is in a definite configuration
> (one of the possible $i \in \mathcal{C}$), and that jumps between configurations at
> random following *ordinary* probabilistic laws.

What is not ordinary is the kind of law. In a Markov process, the probability of going
from $j$ at time $0$ to $i$ at time $t$ can be decomposed through any intermediate time
$t'$:

$$\Gamma(t \leftarrow 0) = \Gamma(t \leftarrow t')\,\Gamma(t' \leftarrow 0).$$

Barandes works with processes in which this decomposition does **not** exist in general.
He calls these processes **indivisible**. The laws only say how to condition on the
initial time, not step by step.

Barandes' central result, the **stochastic-quantum correspondence**
([Barandes, 2023a](https://arxiv.org/abs/2302.10778),
[Barandes, 2023b](https://arxiv.org/abs/2309.03085)), says the following:

- Every unitary quantum evolution defines an indivisible process, through
  $\Gamma_{ij}(t) = |U_{ij}(t)|^2$.
- Every indivisible process can be represented in a Hilbert space, with a unitary
  evolution on a possibly larger configuration space.

Therefore **the two descriptions are equivalent**. According to Barandes, in the
stochastic version:

- The wave function is no longer a physical object and becomes a calculational tool.
- There is no collapse as a physical process: measuring is updating ordinary
  probabilities.
- Interference, entanglement and non-commuting observables **emerge on their own** from
  indivisibility.

## What formalization adds

This section is the motivation of this project, not of Barandes.

The correspondence is a precise mathematical claim, and so it can be verified. There are
three reasons to do it in Lean:

1. **Rigor.** In the foundations of physics it is easy to slip in assumptions without
   noticing. Lean forces every hypothesis to be written down.
2. **Collaboration.** If a theorem compiles, it is correct, no matter who wrote it. This
   lets strangers contribute without anyone having to be trusted.
3. **Extension.** To take the theory further (continuous spaces, fields, relativity), a
   solid base is needed. Each new result builds on the earlier ones, which are already
   verified.

## What this theory is not (yet)

It pays to be honest. Barandes himself presents his formulation as empirically equivalent
to quantum mechanics: as formulated, indivisible stochastic mechanics **makes the same
predictions** as quantum mechanics. So "replacing" quantum mechanics today means replacing
its *ontology*, that is, what exists according to the theory, not its predictions. If
there is new physics, it will show up when exploring the edges: which processes are
physically admissible, what happens with multi-time statistics, how the theory fits with
relativity. That is what Part IV is about.

## Reading

- J. A. Barandes, *The Stochastic-Quantum Correspondence*,
  [arXiv:2302.10778](https://arxiv.org/abs/2302.10778); Philosophy of Physics 3(1): 8
  (2025). The core text.
- J. A. Barandes, *Quantum Systems as Indivisible Stochastic Processes*,
  [arXiv:2507.21192](https://arxiv.org/abs/2507.21192); Stud. Hist. Phil. Sci. 119,
  102213 (2026). A shorter, more conceptual version.
- J. A. Barandes, *The Stochastic-Quantum Theorem*,
  [arXiv:2309.03085](https://arxiv.org/abs/2309.03085). The theorem in detail.
