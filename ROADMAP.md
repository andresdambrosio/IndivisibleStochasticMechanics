# Roadmap

## Phase 0: Foundations (in progress)
- [x] Probability distributions and column-stochastic matrices
- [x] Generalized stochastic processes, division events, divisibility
- [x] Born representation `Γᵢⱼ = |Θᵢⱼ|²`, unistochastic matrices
- [x] Columns of a unitary matrix are unit vectors (`unitary_col_normSq_sum`)
- [x] Use Mathlib's `Matrix.colStochastic` instead of a custom definition

## Phase 1: Quantum → stochastic
- [ ] Unitary evolution `U(t)` induces a generalized stochastic process `Γ(t) = |U(t)|²`
- [ ] Density matrix `ρ(t) = Θ(t) diag(p₀) Θ(t)†` and `pᵢ(t) = ρᵢᵢ(t)`
- [ ] Example: a qubit (`Fin 2`) with an explicit indivisible process
- [ ] Generic unitary dynamics are indivisible (interference ⇒ failure of divisibility)

## Phase 2: Stochastic → quantum (the Stochastic-Quantum Theorem)
- [ ] Every stochastic matrix has a Born representation (`Θᵢⱼ = √Γᵢⱼ`)
- [ ] Dilation: every generalized stochastic process embeds in a unitary process on a
      larger configuration space (arXiv:2309.03085)
- [ ] Gauge freedom of the representation (phases, unitary changes of basis)

## Phase 3: Phenomena
- [ ] Interference as the cross terms of `|Θ|²`
- [ ] Division events ↔ measurement / decoherence, effective collapse
- [ ] Composite systems, entanglement, and Bell-type correlations
- [ ] Noncommutative observables from the Hilbert-space representation

## Infrastructure
- [ ] CI (GitHub Actions, `lake build` + no-`sorry` check on main)
- [ ] Blueprint (leanblueprint) linking each paper statement to its Lean declaration
- [ ] Docs via doc-gen4

## Papers to review
- Barandes, *A Deflationary Account of Quantum Theory and its Implications for the Complex Numbers*, arXiv:2602.01043
- *The Born Representation Theorem and the Unistochastic Theorem*, arXiv:2608.04354
- *Quantum Conditional Stochastic Processes*, arXiv:2603.27369
