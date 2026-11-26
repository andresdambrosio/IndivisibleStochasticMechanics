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
- [x] Density matrix `ρ(t) = Θ(t) diag(p₀) Θ(t)†` with `pᵢ(t) = ρᵢᵢ(t)`, and it is a genuine density matrix
- [ ] Generic unitary dynamics are indivisible (interference ⇒ failure of divisibility)

### I.3 Stochastic → quantum: the Stochastic-Quantum Theorem (book ch. 8)
- [x] The marginal of a unitary on system ⊗ environment is stochastic
- [x] Every stochastic matrix has a unitary dilation (environment `Option n`)
- [x] **Flagship theorem, first version:** transition matrices are stochastic at all times
      iff at all times they are unitary marginals
      (`forall_mem_colStochastic_iff_exists_isUnitaryDilation`)
- [ ] Every stochastic matrix has a Born representation `Θᵢⱼ = √Γᵢⱼ` (issue #3)
- [ ] Strengthen the dilation: `U(0) = 1`, and `U(t)` continuous in `t` when `Γ(t)` is
- [ ] Smaller environments: when does an environment of size `n`, or none, suffice?
- [ ] Compare with Barandes' exact statement in arXiv:2309.03085 and formalize it verbatim
- [ ] Gauge freedom: phases and changes of basis that leave `Γ` invariant

### I.4 Quantum phenomena from the stochastic side
- [ ] Interference as the cross terms of `|Θ|²`
- [x] Collapse as the creation of division events (book ch. 10)
- [x] Decoherence as the creation of division events (book ch. 10)
- [ ] Composite systems and entanglement
- [ ] Noncommutative observables from the Hilbert-space representation
- [ ] The role of complex numbers (arXiv:2602.01043)

## Stage II: Complete the dictionary with textbook quantum mechanics

"All of quantum mechanics" means, in increasing difficulty:

1. **Finite dimensions, closed systems:** unitary evolution. *(Stage I, nearly done.)*
2. **Finite dimensions, everything else:** density matrices, quantum channels, measurement
   of arbitrary observables (POVMs), composite systems. Mathlib has what we need.
3. **Infinite dimensions:** particles in ℝ³, unbounded observables like position,
   momentum and energy. This **needs new Mathlib infrastructure**, which we build
   ourselves in `ForMathlib/` and upstream. See `ForMathlib/README.md`.
4. **Fields:** QFT. See Stage III.

### II.1 Finite dimensions, everything else (book ch. 7, 9, 10)
- [x] Barandes' density matrix is a density matrix whose diagonal is the stochastic distribution
- [x] Quantum channels (Kraus form) induce stochastic matrices
- [x] Every stochastic matrix is induced by a quantum channel (classical Kraus operators)
- [x] Every non-degenerate observable admits an ideal (von Neumann) measurement interaction
- [x] **Born rule for arbitrary observables, derived:** pointer-configuration probabilities
      equal `‖⟨v a, ψ⟩‖²`
- [ ] Degenerate observables (projectors of higher rank)
- [ ] Non-ideal measurements and POVMs
- [x] **Collapse, derived:** after evolve–measure–evolve, `P(i, a | j) = |(W v_a)ᵢ|² · |⟨v_a|U|j⟩|²`;
      later evolution depends only on the recorded outcome (`collapse_apply`)
- [x] Measurement removes interference: `Γ_sys = |W V|² · |Vᴴ U|²`
- [x] **Collapse as a division event:** measuring the configuration at `t₁` makes `t₁` a
      division event, for any unitary dynamics (`measuredAt_isDivisionEvent`); for the qubit,
      measuring at `π/4` turns a non-division time into a division event
- [ ] Division events from measurements of arbitrary observables (`V ≠ 1`), and repeated
      measurements
- [x] **Decoherence:** an environment that records configurations perfectly creates a
      division event, with no one reading it (`recordedAt_isDivisionEvent`); the general
      formula weights interference by the overlaps of the records
- [x] Partial decoherence of the qubit: swap probability `(1 + cos θ)/2`, and `π/4` is a
      division event iff the record is perfect
- [ ] Continuous decoherence: records that build up over time, and approximate division
      events (a quantitative notion of "almost divisible")
- [ ] Composite systems, entanglement, Bell/CHSH and the Tsirelson bound

### II.2 Infrastructure for infinite dimensions (in `ForMathlib/`, to be upstreamed)
- [ ] Spectral measures; the spectral theorem for unbounded self-adjoint operators
- [ ] Stone's theorem: strongly continuous unitary groups ↔ self-adjoint generators
- [ ] Strongly continuous (C₀) semigroups
- [ ] Density operators and channels on separable Hilbert spaces

### II.3 Infinite dimensions, physics

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
- [ ] **No autonomous law for Γ:** there are unitaries with `|A|² = |A′|²` but `|BA|² ≠ |BA′|²`,
      so `Γ(t₁)` never determines `Γ(t)`. The phases are necessary memory. What is the
      *minimal* memory? Is real data enough (Madelung, Nelson; Wallstrom's objection), or is
      the full complex structure needed (arXiv:2602.01043)?

## Stage IV: Community and infrastructure

- [x] CI: `lake build` on every push and pull request
- [x] Book in Markdown (`book/`) explaining every step, written for a course
- [x] Book published on GitHub Pages (mdBook + KaTeX)
- [x] `CONTRIBUTING.md`: AI-first model (free proofs, trusted definitions)
- [x] Trusted layer `TRUSTED.md`, with CI enforcing that every definition is listed
- [ ] Human review of every ⏳ entry in `TRUSTED.md`, including references
- [x] `ForMathlib/` directory for general results to upstream to Mathlib
- [ ] First upstream PR to Mathlib (`Matrix.exists_mem_unitaryGroup_of_orthonormal`)
- [x] CI check that `main` has no warnings and no `sorry` (`lake build --wfail`)
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
