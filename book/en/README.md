# Indivisible Stochastic Mechanics

### A course that builds Jacob Barandes' stochastic reformulation of quantum mechanics step by step, with proofs verified in Lean

**Andrés D'Ambrosio**

> *Leé este libro en español con el botón **ES** de arriba a la derecha.*

## Authorship and credits

Quantum mechanics as indivisible stochastic processes was proposed by
**Jacob A. Barandes** ([arXiv:2302.10778](https://arxiv.org/abs/2302.10778),
[arXiv:2309.03085](https://arxiv.org/abs/2309.03085),
[arXiv:2507.21192](https://arxiv.org/abs/2507.21192)). The central ideas of this book are
his, and also those of the classic authors cited in each chapter (Born, von Neumann,
Stinespring, Kraus, Zurek and others).

This book and the Lean formalization are by **Andrés D'Ambrosio**, written with heavy use
of AI (see the [preface](00-preface.md)). Each chapter cites the source of every result,
and states explicitly what is an original contribution of the project. The full list is in
the [references](99-references.md).

The book accompanies the repository. Each chapter explains the physics, the mathematics
and the Lean code of one stretch of the project, and the book grows with the code.
Chapters marked ✅ match code that is already verified. Chapters marked 🚧 are plans.

## Contents

**Part I: Starting point**

0. ✅ [Preface: what this book is and how to read it](00-preface.md)
1. ✅ [Why reformulate quantum mechanics](01-motivation.md)
2. ✅ [Lean for physicists, the bare minimum](02-lean-for-physicists.md)

**Part II: The stochastic foundations**

3. ✅ [Probabilities and stochastic matrices](03-stochastic-matrices.md)
4. ✅ [Indivisible processes and division events](04-indivisible-processes.md)
5. ✅ [The Born representation and unitary evolution](05-born-representation.md)
6. ✅ [The indivisible qubit: interference seen from the stochastic side](06-indivisible-qubit.md)

**Part III: The full correspondence**

7. ✅ [Density matrices and quantum channels](07-density-matrices-and-channels.md)
8. ✅ [The stochastic-quantum theorem: from processes to Hilbert spaces](08-stochastic-quantum-theorem.md)
9. ✅ [Measurement and the Born rule](09-measurement-and-born-rule.md)
10. ✅ [Collapse and decoherence as division events](10-collapse-and-decoherence.md)
11. ✅ [Composite systems and entanglement](11-composite-systems.md)

**Part IV: Beyond** 🚧

12. 🚧 Continuous configuration spaces
13. 🚧 Towards relativity and fields
14. 🚧 Open problems

[References](99-references.md)

## Conventions

- Names of Lean declarations are in `monospace`, for example
  `ISM.Qubit.process_isIndivisible`. You can search for them directly in the code.
- **Column**-stochastic matrices: $\Gamma_{ij}$ is the probability of ending in $i$ having
  started in $j$.
- Units with $\hbar = 1$.
