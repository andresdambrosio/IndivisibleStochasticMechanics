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

## Status

Early. See [ROADMAP.md](ROADMAP.md) for the full plan.

| Module | Contents |
|---|---|
| `Stochastic/Basic` | probability distributions; evolution under Mathlib's `colStochastic` matrices |
| `Stochastic/Indivisible` | generalized stochastic processes, division events, (in)divisibility |
| `Stochastic/Unistochastic` | Born representations, unistochastic ⇒ stochastic |
| `Quantum/UnitaryProcess` | unitary evolution ⇒ generalized stochastic process |
| `Examples/Qubit` | a qubit under `H = σₓ` whose process is provably indivisible |

## The book

[`book/`](book/README.md) is a step-by-step course, in Spanish, that explains the physics,
the mathematics and the Lean code as the project grows.

## Building

```bash
# install elan (Lean toolchain manager) once: https://lean-lang.org/install
lake exe cache get   # download prebuilt Mathlib
lake build
```

## Contributing

Pick an unchecked item from the roadmap, open an issue, and send a PR. Every definition
should cite the paper and section it comes from. `main` must build with no `sorry`.

## References

* J. A. Barandes, *The Stochastic-Quantum Correspondence*, Philosophy of Physics 3(1) (2025);
  [arXiv:2302.10778](https://arxiv.org/abs/2302.10778)
* J. A. Barandes, *The Stochastic-Quantum Theorem*, [arXiv:2309.03085](https://arxiv.org/abs/2309.03085)
* J. A. Barandes, *Quantum Systems as Indivisible Stochastic Processes*, Stud. Hist. Phil. Sci. (2026);
  [arXiv:2507.21192](https://arxiv.org/abs/2507.21192)
* Related Lean physics effort: [physlib](https://github.com/leanprover-community/physlib)

## License

Apache 2.0
