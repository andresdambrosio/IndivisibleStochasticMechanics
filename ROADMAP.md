# Roadmap

The long-term goal is to show, with machine-checked proofs, that **Indivisible Stochastic
Mechanics (ISM)** can do everything textbook quantum mechanics does. The starting point
is Jacob Barandes' stochastic-quantum correspondence. After that we want to find out
where the stochastic picture is *more* general or *more* useful.

There are two different goals, and we keep them apart:

1. **Conceptual replacement.** The stochastic formulation is empirically equivalent to
   quantum theory. Formalization makes this equivalence precise and checkable.
2. **New physics.** Find out whether, and where, the stochastic picture predicts
   something different or is strictly more expressive. This is open research.

Legend: `[x]` done (in Lean, no `sorry`), `[ ]` to do. The book chapter that explains
each item is in parentheses.

---

## Stage I: Formalize Barandes' published results

### I.1 Foundations (book ch. 3–5)
- [x] Probability distributions; evolution under Mathlib's `Matrix.colStochastic`
- [x] Generalized stochastic processes `Γ(t ← 0)`, division events, (in)divisibility
- [x] Born representations `Γᵢⱼ = |Θᵢⱼ|²`, unistochastic matrices
- [x] Unistochastic ⇒ stochastic (columns of a unitary are unit vectors)

### I.2 Quantum → stochastic (book ch. 5–6)
- [x] A unitary evolution `U(t)` with `U(0) = 1` induces a generalized stochastic process
- [x] Example: a qubit under `H = σₓ` whose process is indivisible (`π/4` is not a division event)
- [ ] Qubit: no `t' ∈ (0, π/2)` is a division event, and `π/2` is one
- [ ] Hamiltonian evolution `U(t) = exp(-itH)` via Mathlib's `NormedSpace.exp`
- [ ] Density matrix `ρ(t) = Θ(t) diag(p₀) Θ(t)†` with `pᵢ(t) = ρᵢᵢ(t)`
- [ ] Generic unitary dynamics are indivisible (interference ⇒ failure of divisibility)

### I.3 Stochastic → quantum: the Stochastic-Quantum Theorem
- [ ] Every stochastic matrix has a Born representation `Θᵢⱼ = √Γᵢⱼ`
- [ ] Every generalized stochastic process has a unitary dilation on a larger
      configuration space (arXiv:2309.03085)
- [ ] Gauge freedom: phases and changes of basis that leave `Γ` invariant
- [ ] **Flagship theorem:** the stochastic-quantum correspondence in both directions,
      for finite configuration spaces

### I.4 Quantum phenomena from the stochastic side
- [ ] Interference as the cross terms of `|Θ|²`
- [ ] Decoherence as the creation of division events
- [ ] Measurement: the Born rule and "collapse" as conditioning at a division event
- [ ] Composite systems and entanglement
- [ ] Noncommutative observables from the Hilbert-space representation
- [ ] The role of complex numbers (arXiv:2602.01043)

## Stage II: Complete the dictionary with textbook quantum mechanics

- [ ] Continuous configuration spaces (ℝ, ℝ³) using Mathlib's measure theory and
      Markov kernels (`ProbabilityTheory.Kernel`)
- [ ] Where does the Schrödinger equation come from? The stochastic counterpart of the
      Hamiltonian, i.e. what principle selects `Γ(t)`
- [ ] Worked systems: harmonic oscillator, hydrogen atom, spin-½
- [ ] Identical particles: bosons and fermions as configuration-space structure
- [ ] Bell, CHSH and the Tsirelson bound, formally verified

## Stage III: Extend the theory (open research)

- [ ] Relativity and quantum field theory: what is the configuration space of a field,
      and how is Lorentz invariance guaranteed?
- [ ] Locality: a precise, formal statement of Barandes' claim of a causally local account
- [ ] Multi-time statistics: the theory leaves multi-time joint probabilities
      unspecified. Should they be fixed, and would fixing them change predictions?
- [ ] Open systems and thermodynamics: link to non-Markovian dynamics and CP-divisibility
- [ ] Which indivisible processes are "physical"? If only a subclass, there may be new physics

## Stage IV: Community and infrastructure

- [x] CI: `lake build` on every push and pull request
- [x] Book in Markdown (`book/`) explaining every step, written for a course
- [ ] CI check that `main` contains no `sorry`
- [ ] Blueprint (leanblueprint) linking each paper statement to its Lean declaration
- [ ] API docs with doc-gen4, published on GitHub Pages
- [ ] Coordinate with [physlib](https://github.com/leanprover-community/physlib) and the
      Lean Zulip, and upstream general results to Mathlib or physlib
- [ ] Label `good first issue` tasks for physicists learning Lean
- [ ] Reach out to Jacob Barandes once the flagship theorem is verified

---

## Related work

- **Barandes' papers:** arXiv:2302.10778, 2309.03085, 2507.21192, 2602.01043
- **Follow-ups:** S. Calvo, *On the stochastic-quantum correspondence* (arXiv:2601.18720);
  *Quantum Conditional Stochastic Processes* (arXiv:2603.27369);
  *The Born Representation Theorem and the Unistochastic Theorem* (arXiv:2608.04354)
- **Other formalization:** A. Horsocrates, *From Distinction to Unistochasticity*, says it
  has theorems checked in Rocq/Coq (not yet verified by us)
- **Numerical:** [isp-lab](https://github.com/mrklaney/isp-lab), a Python lab for divisibility checks
- **Lean physics:** [physlib](https://github.com/leanprover-community/physlib) (PhysLean +
  Lean-QuantumInfo); Lean-Quantum (arXiv:2607.05492); a Lean formalization of a free
  Euclidean QFT (arXiv:2603.15770)
