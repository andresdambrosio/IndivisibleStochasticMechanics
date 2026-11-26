# NewQuantumMechanics

A community project to **formalize Jacob Barandes' indivisible-stochastic reformulation of
quantum mechanics in Lean 4**, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

Think of it as *mathlib for one foundations-of-physics program*: every definition and
theorem in the stochastic-quantum correspondence gets stated precisely and checked by
machine.

## The physics in one paragraph

Barandes argues that every quantum system can be understood as a stochastic process on an
ordinary configuration space, governed by **indivisible** transition laws
`Γ(t ← 0)`. These laws need not factor through intermediate times, unlike Markov
processes. The *stochastic-quantum correspondence* says such processes and unitary
quantum theory are equivalent descriptions. The link is the Born-type relation
`Γᵢⱼ(t) = |Θᵢⱼ(t)|²`. In this picture the wave function, Hilbert space and collapse are
secondary mathematical tools rather than physical ingredients.

## Status

Early. See [ROADMAP.md](ROADMAP.md).

| Module | Contents |
|---|---|
| `Stochastic/Basic` | probability distributions, column-stochastic matrices, closure under products |
| `Stochastic/Indivisible` | generalized stochastic processes, division events, (in)divisibility |
| `Stochastic/Unistochastic` | Born representations, unistochastic ⇒ stochastic |

## Building

```bash
# install elan (Lean toolchain manager) once: https://lean-lang.org/install
lake exe cache get   # download prebuilt Mathlib
lake build
```

## Contributing

Pick an item from the roadmap or any `sorry` in the code, open an issue, and send a PR.
Every definition should cite the paper and section it comes from.

## References

* J. A. Barandes, *The Stochastic-Quantum Correspondence*, Philosophy of Physics 3(1) (2025);
  [arXiv:2302.10778](https://arxiv.org/abs/2302.10778)
* J. A. Barandes, *The Stochastic-Quantum Theorem*, [arXiv:2309.03085](https://arxiv.org/abs/2309.03085)
* J. A. Barandes, *Quantum Systems as Indivisible Stochastic Processes*,
  [arXiv:2507.21192](https://arxiv.org/abs/2507.21192)
* Related Lean physics effort: [physlib](https://github.com/leanprover-community/physlib)
  (formerly PhysLean / HepLean)

## License

Apache 2.0
