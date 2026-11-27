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
- [x] Qubit: no `t' ∈ (0, π/2)` is a division event, and `π/2` is one; the division events
      are exactly the multiples of `π/2` (`isDivisionEvent_iff_exists_nat`, book ch. 6).
      *Known:* a special case of Pimenta's characterization of divisible two-configuration
      dynamics ([arXiv:2505.08785](https://arxiv.org/abs/2505.08785))
- [x] Hamiltonian evolution `U(t) = exp(-itH)` via Mathlib's `NormedSpace.exp`: unitary,
      group law, induced process; the qubit's `U` is `exp(-itσₓ)` (book ch. 5–6)
- [x] Density matrix `ρ(t) = Θ(t) diag(p₀) Θ(t)†` with `pᵢ(t) = ρᵢᵢ(t)`, and it is a genuine density matrix
- [ ] Generic unitary dynamics are indivisible (interference ⇒ failure of divisibility).
      *Known, to formalize:* the classical reduction of a unitary dynamics loses
      P-divisibility (Benatti, Chruściński, Nichele, PRA 110, 052212 (2024),
      [arXiv:2405.05794](https://arxiv.org/abs/2405.05794)); Barandes discusses why
      intermediate times of a unistochastic evolution are generically not division events
      ([arXiv:2507.21192](https://arxiv.org/abs/2507.21192)). Check the exact statements
      before formalizing

### I.3 Stochastic → quantum: the Stochastic-Quantum Theorem (book ch. 8)
- [x] The marginal of a unitary on system ⊗ environment is stochastic
- [x] Every stochastic matrix has a unitary dilation (environment `Option n`)
- [x] **Flagship theorem, first version:** transition matrices are stochastic at all times
      iff at all times they are unitary marginals
      (`forall_mem_colStochastic_iff_exists_isUnitaryDilation`)
- [ ] Every stochastic matrix has a Born representation `Θᵢⱼ = √Γᵢⱼ` (issue #3)
- [ ] Strengthen the dilation: `U(0) = 1`, and `U(t)` continuous in `t` when `Γ(t)` is
- [ ] Smaller environments: when does an environment of size `n`, or none, suffice?
      *Known bounds:* Barandes' Stinespring construction needs dimension at most `N³`
      ([arXiv:2602.01043](https://arxiv.org/abs/2602.01043) §5); ours uses `N(N + 1)`.
      With no environment the question is unistochasticity, which is characterized for
      `N = 3` but open in general for `N ≥ 4`
- [ ] Compare with Barandes' exact statement in arXiv:2309.03085 and formalize it verbatim
- [ ] Gauge freedom: moved to Stage V

### I.4 Quantum phenomena from the stochastic side
- [ ] Interference as the cross terms of `|Θ|²`
- [x] Collapse as the creation of division events (book ch. 10)
- [x] Decoherence as the creation of division events (book ch. 10)
- [x] Composite systems: independent systems give the product process, and common division
      events survive (book ch. 11)
- [x] No signalling: local unitaries on one system do not change the other's statistics
- [x] Entanglement, stochastically: a Bell pair's correlations survive a local change of
      basis only without a division event (book ch. 11)
- [ ] Noncommutative observables from the Hilbert-space representation
- [ ] The role of complex numbers: moved to Stage V

## Stage II: Complete the dictionary with textbook quantum mechanics

"All of quantum mechanics" means, in increasing difficulty:

1. **Finite dimensions, closed systems:** unitary evolution. *(Stage I, nearly done.)*
2. **Finite dimensions, everything else:** density matrices, quantum channels, measurement
   of arbitrary observables (POVMs), composite systems. Mathlib has what we need.
3. **Infinite dimensions:** particles in ℝ³, unbounded observables like position,
   momentum and energy. This **needs new Mathlib infrastructure**, which we build
   ourselves in `ForMathlib/` and upstream. See `ForMathlib/README.md`.
4. **Fields:** QFT. See Stage III.

### II.1 Finite dimensions, everything else (book ch. 7, 9, 10, 11)
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
- [x] **Approximate division events** (original to this project): `divisionDefect`, zero iff
      division event; a record with overlaps `≤ ε` gives defect `≤ (N − 1) ε / 2`, attained
      by the qubit (`|cos θ| / 2`) (book ch. 10). Still to do: relate it to `qCor` and to
      RHP. Background: Barandes, Hasan and
      Kagan say division events "are often only approximate or effective" and hold up to
      "some given level of precision", but give no measure (PRA 114, 022208 (2026),
      [arXiv:2512.18105](https://arxiv.org/abs/2512.18105) §3.1; their discrepancy `qCor`,
      eqs. 19–20). RHP divisibility measure: Rivas, Huelga, Plenio, PRL 105, 050403 (2010).
      No measure adapted to Barandes' definition was found in the literature (search of
      November 2026)
- [ ] Continuous decoherence: records that build up over time, and division events that
      become exact only in the limit. With `M` independent records the overlap is a product,
      so the defect bound decays like `εᴹ` (Joos–Zeh); formalize that
- [x] Composite systems and a Bell pair (book ch. 11)
- [x] No signalling for any local operation (unitary on system + own ancilla), in particular
      local measurements with an apparatus (book ch. 11)
- [x] CHSH inequality for local hidden-variable models, Tsirelson's bound `2√2`, and the
      Bell pair reaching it (book ch. 11)
- [x] Tsirelson's bound stated directly for the transition probabilities of a composite
      process (any unitary preparation, local unitaries, `±1` outcomes)
- [x] Bell/CHSH with explicit local measurement apparatuses (ch. 9): the pointers'
      distribution equals rotate-then-read, Tsirelson holds, and the Bell pair reaches `2√2`

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
- [x] Bell, CHSH and the Tsirelson bound, formally verified

## Stage III: Extend the theory (open research)

- [ ] Relativity and quantum field theory: what is the configuration space of a field,
      and how is Lorentz invariance guaranteed?
- [ ] Locality: a precise, formal statement of Barandes' claim of a causally local account
- [ ] Multi-time statistics: the theory leaves multi-time joint probabilities
      unspecified. Should they be fixed, and would fixing them change predictions?
- [ ] Open systems and thermodynamics: link to non-Markovian dynamics and CP-divisibility
- [ ] Which indivisible processes are "physical"? If only a subclass, there may be new physics
- [ ] No autonomous law for Γ: moved to Stage V

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

## Stage V: Without the Hilbert space, and without complex numbers (last)

In indivisible stochastic mechanics, everything physical is real: configurations, and the
stochastic matrices `Γ(t)`. Complex numbers only appear in the Hilbert-space representation
`Γ = |Θ|²`. **Working hypothesis (Andrés D'Ambrosio):** the complex numbers play a fictitious,
bookkeeping role, and the theory can be stated, computed and used without them.

What is already known, and what any answer has to respect:

- Barandes argues that the Hilbert-space formalism is a Markovian embedding of an
  indivisible process, and that complex numbers are what make that embedding work
  ([arXiv:2602.01043](https://arxiv.org/abs/2602.01043), *A Deflationary Account of
  Quantum Theory and its Implications for the Complex Numbers*). On that view they belong
  to the representation, not to the ontology. That is close to the hypothesis above.
- Renou et al. showed that quantum theory over the **real** numbers, with the standard
  tensor-product rule for independent sources, makes different predictions in network
  scenarios ([Nature 600, 625 (2021)](https://doi.org/10.1038/s41586-021-04160-4)).
  Experiments favour the complex theory
  ([Chen et al., PRL 128, 040403 (2022)](https://doi.org/10.1103/PhysRevLett.128.040403);
  [Li et al., PRL 128, 040402 (2022)](https://doi.org/10.1103/PhysRevLett.128.040402)).
  So "replace ℂ by ℝ in the Hilbert space" does not work. A real reformulation has to
  change something else, for example how composite systems are put together.
- Real hydrodynamic reformulations (Madelung) are not equivalent to the Schrödinger
  equation without an extra quantization condition
  ([Wallstrom, PRA 49, 1613 (1994)](https://doi.org/10.1103/PhysRevA.49.1613)).

Tasks:

- [ ] **No autonomous law for Γ:** there are unitaries with `|A|² = |A′|²` but
      `|BA|² ≠ |BA′|²`, so `Γ(t₁)` alone never determines `Γ(t)`. Some memory beyond `Γ`
      is necessary.
- [ ] **Gauge freedom:** exactly which data of `Θ` are fixed by the whole family `Γ(t)`
      (phases, changes of basis).
- [ ] **Trading ℂ for a hidden bit** (*known, to formalize*): every complex unitary
      `U = A + iB` gives a real orthogonal matrix `[[A, -B], [B, A]]` on `n × Bool`, and `Γ`
      is the marginal of its Born matrix. This is the real representation of quantum theory
      (Stueckelberg, Helv. Phys. Acta 33, 727 (1960); Myrheim, arXiv:quant-ph/9905037), and
      Barandes uses it in the stochastic setting
      ([arXiv:2507.21192](https://arxiv.org/abs/2507.21192) §4.2). Barandes argues that the
      bit's structure `I` (with `I² = −1`) *is* ℂ in disguise
      ([arXiv:2602.01043](https://arxiv.org/abs/2602.01043) §2).
- [ ] **Composite systems** (*known, to formalize*): one *shared* rebit suffices to simulate
      any multipartite quantum system, while one bit per subsystem does not (McKague, Mosca,
      Gisin, PRL 102, 020505 (2009), [arXiv:0810.1923](https://arxiv.org/abs/0810.1923)).
      Renou et al. show that the local version is experimentally distinguishable. Formalize
      the shared-bit construction for composite processes.
- [ ] **Real dilations of families** (candidate original result). Instant by instant, every
      stochastic matrix is the marginal of a *real* orthogonal matrix (our `Option n`
      dilation has real columns `√Γᵢⱼ`), so complex numbers are never needed at a single
      time. The question is for whole families: when is `Γ(t)` the marginal of a real
      orthogonal *one-parameter group* `exp(tA)`, of what minimal dimension, and must `A`
      always commute with a complex structure `J` (`J² = −1`)? A theorem of that form would
      make precise Barandes' claim that any real structure doing the job is isomorphic to ℂ
      ([arXiv:2602.01043](https://arxiv.org/abs/2602.01043) §5, which argues from
      orthostochasticity at size `N` only). Related: in real Hilbert space, Stueckelberg
      obtains an operator playing the role of `i` from an uncertainty principle (1960), and
      Moretti and Oppio obtain the complex structure from Poincaré symmetry
      ([arXiv:1611.09029](https://arxiv.org/abs/1611.09029)).
- [ ] **Minimal memory** (open): what is the smallest real structure that, together with
      `Γ(t₁)`, determines the future? Is it less than a complex phase per entry? Closest
      work: Doukas argues that phases act as a compressed record of earlier context, and
      that a revival of distinguishability rules out Markovian realizers, but proves no
      bound ([arXiv:2611.32578](https://arxiv.org/abs/2611.32578),
      [arXiv:2602.22095](https://arxiv.org/abs/2602.22095)).
- [ ] **Without the Hilbert space:** state and prove the main results of the book
      (interference, collapse, decoherence, Bell) using only real stochastic data plus that
      memory.

---

## Related work

- **Barandes' papers:** arXiv:2302.10778, 2309.03085, 2402.16935, 2507.21192, 2602.01043;
  with Hasan and Kagan, *The CHSH Game, Tsirelson's Bound, and Causal Locality*
  (arXiv:2512.18105)
- **Follow-ups:** S. Calvo, *On the stochastic-quantum correspondence* (arXiv:2601.18720);
  *Quantum Conditional Stochastic Processes* (arXiv:2603.27369);
  *The Born Representation Theorem and the Unistochastic Theorem* (arXiv:2608.04354);
  L. S. Pimenta, *Divisible and indivisible Stochastic-Quantum dynamics* (arXiv:2505.08785);
  J. Doukas, arXiv:2602.22095 and arXiv:2611.32578
- **Non-Markovianity and divisibility:** Rivas, Huelga, Plenio, PRL 105, 050403 (2010)
  (arXiv:0911.4270, the RHP measure); Vacchini et al., NJP 13, 093004 (2011); Benatti,
  Chruściński, Nichele (arXiv:2405.05794); Milz et al., PRX 10, 041049 (2020)
- **Real quantum theory:** Stueckelberg, Helv. Phys. Acta 33, 727 (1960); Myrheim
  (arXiv:quant-ph/9905037); McKague, Mosca, Gisin (arXiv:0810.1923); Aleksandrova, Borish,
  Wootters, *Real-vector-space quantum theory with a universal quantum bit*
  (arXiv:1210.4535); Moretti, Oppio (arXiv:1611.09029); Renou et al., Nature 600, 625 (2021)
- **Other formalization:** A. Horsocrates, *From Distinction to Unistochasticity*, says it
  has theorems checked in Rocq/Coq (not yet verified by us)
- **Numerical:** [isp-lab](https://github.com/mrklaney/isp-lab), a Python lab for divisibility checks
- **Lean physics:** [physlib](https://github.com/leanprover-community/physlib) (PhysLean +
  Lean-QuantumInfo); Lean-Quantum (arXiv:2607.05492); a Lean formalization of a free
  Euclidean QFT (arXiv:2603.15770)
