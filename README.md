# Indivisible Stochastic Mechanics

A community project to **formalize Jacob Barandes' indivisible-stochastic reformulation of
quantum mechanics in Lean 4**, and then extend it. It is built on
[Mathlib](https://github.com/leanprover-community/mathlib4).

Think of it as *mathlib for one foundations-of-physics program*: every definition and
theorem of the stochastic-quantum correspondence is stated precisely and checked by
machine.

## The physics in one paragraph

Barandes argues that every quantum system can be understood as a stochastic process on an
ordinary configuration space, governed by **indivisible** transition laws `Γ(t ← 0)`.
Unlike Markov processes, these laws need not factor through intermediate times. The
*stochastic-quantum correspondence* says such processes and unitary quantum theory are
equivalent descriptions, linked by the Born-type relation `Γᵢⱼ(t) = |Θᵢⱼ(t)|²`. In this
picture the wave function, Hilbert space and collapse are mathematical tools rather than
physical ingredients.

## How we work: AI-first, with a trusted layer

AI tools write as much as possible, proofs included, at any scale: Lean checks every
proof. What Lean cannot check is whether a *definition* means what the physics says. So
every definition and main statement is listed in [TRUSTED.md](TRUSTED.md), with its
source and a human-review status, and CI enforces that the list is complete. See
[CONTRIBUTING.md](CONTRIBUTING.md).

## Status

Early. See [ROADMAP.md](ROADMAP.md) for the full plan.

| Module | Contents |
|---|---|
| `Stochastic/Basic` | probability distributions; evolution under Mathlib's `colStochastic` matrices |
| `Stochastic/Indivisible` | generalized stochastic processes, division events, (in)divisibility |
| `Stochastic/Unistochastic` | Born representations, unistochastic ⇒ stochastic |
| `Quantum/UnitaryProcess` | unitary evolution ⇒ generalized stochastic process |
| `Examples/Qubit` | a qubit under `H = σₓ` whose process is provably indivisible |
| `Quantum/Dilation` | **stochastic-quantum correspondence (finite dimensions)**: every stochastic process is the marginal of a unitary evolution on a larger system |
| `Quantum/DensityMatrix` | Barandes' density matrix `Θ diag(p) Θᴴ`: a genuine density matrix whose diagonal is the stochastic distribution |
| `Quantum/Channel` | quantum channels ⇔ stochastic matrices |
| `Quantum/Measurement` | **the Born rule for arbitrary observables, derived** from pointer-configuration probabilities |
| `Quantum/Collapse` | **collapse as a division event**: after a measurement, later evolution depends only on the outcome, and interference between outcomes disappears |
| `Examples/MeasuredQubit` | measuring the qubit at `π/4` turns a non-division time into a division event |
| `Quantum/Decoherence` | **decoherence creates division events**: an environment that records the configuration removes interference, with no one reading it |
| `Examples/DecoheredQubit` | partial decoherence of the qubit: a division event appears iff the record is perfect |
| `ForMathlib/` | general results we build for Mathlib and upstream ([details](IndivisibleStochasticMechanics/ForMathlib/README.md)) |

## The book

**[Read it online](https://andresdambrosio.github.io/IndivisibleStochasticMechanics/)**.
It is a step-by-step course, in Spanish, that explains the physics, the mathematics and
the Lean code as the project grows. Sources are in [`book/`](book/README.md).

## Building

```bash
# install elan (Lean toolchain manager) once: https://lean-lang.org/install
lake exe cache get   # download prebuilt Mathlib
lake build
```

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md). Good places to start are the issues labelled
[`good first issue`](https://github.com/andresdambrosio/IndivisibleStochasticMechanics/labels/good%20first%20issue).

## References

* J. A. Barandes, *The Stochastic-Quantum Correspondence*, Philosophy of Physics 3(1) (2025);
  [arXiv:2302.10778](https://arxiv.org/abs/2302.10778)
* J. A. Barandes, *The Stochastic-Quantum Theorem*, [arXiv:2309.03085](https://arxiv.org/abs/2309.03085)
* J. A. Barandes, *Quantum Systems as Indivisible Stochastic Processes*, Stud. Hist. Phil. Sci. (2026);
  [arXiv:2507.21192](https://arxiv.org/abs/2507.21192)
* Related Lean physics effort: [physlib](https://github.com/leanprover-community/physlib)

## License

Code: Apache 2.0 ([LICENSE](LICENSE)). Book: CC BY 4.0 ([book/LICENSE](book/LICENSE)).
