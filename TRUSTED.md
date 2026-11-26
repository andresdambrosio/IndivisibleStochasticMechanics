# The trusted layer

Lean guarantees that every proof in this repository is correct. It **cannot** guarantee
that a definition, or the statement of a main theorem, means what the physics says it
means. This file lists exactly those declarations: the *trusted layer*. It is the only
part of the project that needs human review.

- Every `def` and `structure` in the library must appear here. CI enforces this with
  `scripts/check_trusted.py`.
- Main theorems are added here by humans when their *statement* carries physical meaning.
- Status: ✅ reviewed by a human (name and date) · ⏳ pending human review.

To review an entry: read the Lean statement, compare it with the cited source, write down
any interpretive choice in "Notes", and change the status to ✅ with your name and date.

## Definitions

| Declaration | What it is meant to capture | Source | Notes | Status |
|---|---|---|---|---|
| `ISM.IsProbDist` | a probability distribution on a finite configuration space | standard | | ⏳ |
| `ISM.GenStochasticProcess` | cumulative transition matrices `Γ(t ← 0)`, stochastic for `t ≥ 0`, with `Γ(0) = 1` | arXiv:2302.10778 | `Γ` is defined for every real `t`, but only `t ≥ 0` is constrained | ⏳ |
| `ISM.GenStochasticProcess.IsDivisionEvent` | `t'` is a time through which the dynamics factor stochastically | arXiv:2302.10778 | **Interpretive choice:** one family `Δ(t)` must work for *all* `t ≥ t'` | ⏳ |
| `ISM.GenStochasticProcess.IsDivisible` | every `t' ≥ 0` is a division event (Markovian case) | arXiv:2302.10778 | | ⏳ |
| `ISM.GenStochasticProcess.IsIndivisible` | not divisible | arXiv:2302.10778 | "indivisible" means *some* time fails, not *every* time | ⏳ |
| `ISM.GenStochasticProcess.evolve` | `p(t) = Γ(t) p(0)` | arXiv:2302.10778 | | ⏳ |
| `ISM.IsBornRep` | `Γᵢⱼ = ‖Θᵢⱼ‖²` | arXiv:2309.03085 | | ⏳ |
| `ISM.IsUnistochastic` | `Γ` has a unitary Born representation | standard | | ⏳ |
| `ISM.GenStochasticProcess.ofUnitary` | the process `Γᵢⱼ(t) = ‖Uᵢⱼ(t)‖²` induced by a unitary evolution | arXiv:2302.10778 | rows and columns of `U` are indexed by the configurations, i.e. the basis is fixed | ⏳ |
| `ISM.Qubit.U` | `exp(-i t σₓ)` | standard | written out explicitly, not via a matrix exponential | ⏳ |
| `ISM.Qubit.process` | the process of the qubit under `H = σₓ` | — | | ⏳ |
| `ISM.IsUnitaryDilation` | `Γ` is the system marginal of a unitary `U` on system ⊗ environment, environment prepared in `e₀` | arXiv:2309.03085 | measurement of the environment is not modelled; we only marginalize over it | ⏳ |
| `ISM.IsDensityMatrix` | a density matrix: positive semidefinite, trace one | standard | | ⏳ |
| `ISM.bornDensity` | Barandes' density matrix `Θ · diag(p) · Θᴴ` | arXiv:2302.10778 | built from a *diagonal* initial state (a mixture of configurations), as in the paper | ⏳ |
| `ISM.IsKrausFamily` | Kraus operators: `∑ Kᴴ K = 1` | standard | finite Kraus index | ⏳ |
| `ISM.krausChannel` | the channel `ρ ↦ ∑ K ρ Kᴴ` | standard | | ⏳ |
| `ISM.krausTransition` | the channel's transition probabilities in the configuration basis, `∑ₖ ‖Kₖᵢⱼ‖²` | standard | | ⏳ |
| `ISM.classicalKraus` | auxiliary: Kraus operators `√Γ_ab ∣a⟩⟨b∣` realizing a stochastic matrix | standard | auxiliary construction | ⏳ |
| `ISM.IsIdealMeasurement` | an ideal (von Neumann) measurement of the observable with eigenbasis the columns of `V`, recorded by a pointer | von Neumann (1932); arXiv:2302.10778 | **Interpretive choice:** an outcome *is* a pointer configuration. Non-degenerate observables only. The pointer has one configuration per outcome plus `ready` | ⏳ |
| `ISM.measurementVec` | auxiliary: columns of the measurement unitary with the pointer ready | — | auxiliary construction | ⏳ |
| `ISM.readyState` | composite state "system in `ψ`, pointer ready" | — | | ⏳ |
| `ISM.measuredEvolution` | evolve the system by `U`, measure with `M`, then evolve the system by `W`; the pointer does not move outside the measurement | arXiv:2302.10778 | **Interpretive choice:** the measurement is instantaneous and the pointer is frozen after it | ⏳ |
| `ISM.normSqMatrix` | the matrix of squared moduli `‖Aᵢⱼ‖²` | standard | | ⏳ |
| `ISM.pointerMarginal` | the system's transition matrix `∑ₚ ‖Θ (i, p) (j, ready)‖²`, summing over the pointer | arXiv:2302.10778 | the pointer always starts ready, so other initial pointer configurations are ignored | ⏳ |
| `ISM.measuredComposite` | composite evolution: `U t ⊗ 1` before `t₁`, then measurement at `t₁`, then `U t U(t₁)† ⊗ 1` | arXiv:2302.10778 | after the measurement the system keeps the *same* Hamiltonian dynamics, now applied from `t₁` | ⏳ |
| `ISM.GenStochasticProcess.measuredAt` | the system's process when its dynamics `U t` is interrupted by a measurement at `t₁ > 0` | arXiv:2302.10778 | | ⏳ |
| `ISM.Qubit.configMeasurement` | an ideal measurement of the qubit's configuration | — | chosen noncomputably; no result depends on the choice | ⏳ |
| `ISM.Qubit.measuredProcess` | the qubit process with a configuration measurement at `π/4` | — | | ⏳ |
| `ISM.IsRecording` | `E` records the system's configuration `k` in the environment state `φ k`, leaving the configuration unchanged | Zurek (2003); arXiv:2302.10778 | **Interpretive choice:** the record is instantaneous and does not disturb the configuration (a "pure decoherence" interaction). Records need not be orthogonal | ⏳ |
| `ISM.overlap` | overlap `⟨φ_l, φ_k⟩ = ∑ₑ φ k e · conj (φ l e)` of two records | standard | | ⏳ |
| `ISM.recordingVec` | auxiliary: columns `\|j⟩ ⊗ \|φ j⟩` of a recording unitary | — | auxiliary construction | ⏳ |
| `ISM.recordedEvolution` | evolve by `U`, record with `E`, evolve by `W`; the environment is frozen otherwise | arXiv:2302.10778 | | ⏳ |
| `ISM.envMarginal` | the system's transition matrix, summing over the environment, environment initially in `e₀` | arXiv:2302.10778 | generalizes `pointerMarginal` to any environment | ⏳ |
| `ISM.recordedComposite` | composite evolution with a recording at `t₁` and the same dynamics before and after | arXiv:2302.10778 | | ⏳ |
| `ISM.GenStochasticProcess.recordedAt` | the system's process when an environment records it at `t₁ > 0` | arXiv:2302.10778 | | ⏳ |
| `ISM.Qubit.recordState` | records `(1, 0)` and `(cos θ, sin θ)` of the qubit's two configurations, overlap `cos θ` | — | | ⏳ |
| `ISM.Qubit.recorder` | a unitary that records the qubit with `recordState θ` | — | chosen noncomputably; no result depends on the choice | ⏳ |
| `ISM.Qubit.decoheredProcess` | the qubit process with a partial record at `π/4` | — | | ⏳ |
| `ISM.GenStochasticProcess.prod` | the process of two independent systems, `Γ(t) = Γ₁(t) ⊗ Γ₂(t)` | standard | "independent" means no interaction at any time | ⏳ |
| `ISM.BellPair.hadamard` | the Hadamard gate `(1/√2)[[1, 1], [1, -1]]` | standard | | ⏳ |
| `ISM.BellPair.cnot` | the CNOT gate `\|a, b⟩ ↦ \|a, b + a⟩` | standard | | ⏳ |
| `ISM.BellPair.prep` | Bell-pair preparation `CNOT · (H ⊗ 1)` | Nielsen–Chuang §1.3.6 | | ⏳ |
| `ISM.dilationVec` | auxiliary: columns `∑ i, √Γᵢⱼ ∣i⟩⊗∣some j⟩` of the dilation | — | auxiliary construction, no physical claim | ⏳ |

## Main theorems

| Declaration | Statement in words | Source | Notes | Status |
|---|---|---|---|---|
| `ISM.IsUnistochastic.mem_colStochastic` | every unistochastic matrix is stochastic | standard | | ⏳ |
| `ISM.Qubit.process_Γ` | for the qubit, `Γ(t) = [[cos²t, sin²t], [sin²t, cos²t]]` | — | | ⏳ |
| `ISM.Qubit.process_isIndivisible` | the qubit's process is indivisible | — | | ⏳ |
| `ISM.forall_mem_colStochastic_iff_exists_isUnitaryDilation` | **stochastic-quantum correspondence (finite dimensions)**: transition matrices are stochastic at all times iff at all times they are unitary marginals | arXiv:2309.03085 | **Weaker than it may sound:** the unitary `U(t)` is chosen independently at each `t`. It need not be continuous, satisfy `U(0) = 1`, or come from a Hamiltonian | ⏳ |
| `ISM.bornDensity_apply_self` | the diagonal of Barandes' density matrix is the stochastic distribution `Γ p` | arXiv:2302.10778 | | ⏳ |
| `ISM.bornDensity_isDensityMatrix` | Barandes' density matrix is a genuine density matrix | arXiv:2302.10778 | | ⏳ |
| `ISM.IsKrausFamily.krausTransition_mem_colStochastic` | every quantum channel induces a stochastic matrix | standard | | ⏳ |
| `ISM.krausTransition_classicalKraus` | every stochastic matrix is induced by a quantum channel | standard | | ⏳ |
| `ISM.exists_isIdealMeasurement` | every (non-degenerate) observable admits an ideal measurement interaction | von Neumann (1932) | | ⏳ |
| `ISM.IsIdealMeasurement.pointer_prob` | **Born rule from configurations:** pointer shows `a` with probability `‖⟨v a, ψ⟩‖²` | arXiv:2302.10778 | | ⏳ |
| `ISM.IsIdealMeasurement.prob_after_evolution` | the same, for a system that starts in configuration `j` and evolves by `U` | arXiv:2302.10778 | | ⏳ |
| `ISM.IsIdealMeasurement.collapse_apply` | **collapse, derived:** after evolve–measure–evolve, the amplitude for (system `i`, pointer `a`) is `(W v_a)ᵢ · ⟨v_a\|U\|j⟩` | arXiv:2302.10778 | | ⏳ |
| `ISM.IsIdealMeasurement.pointerMarginal_measuredEvolution` | measurement removes interference: `Γ_sys = \|W V\|² · \|Vᴴ U\|²` | arXiv:2302.10778 | | ⏳ |
| `ISM.GenStochasticProcess.measuredAt_isDivisionEvent` | **collapse as a division event:** measuring the configuration at `t₁` makes `t₁` a division event, for any unitary dynamics | arXiv:2302.10778 | only for measurements of the configuration (`V = 1`) | ⏳ |
| `ISM.IsRecording.envMarginal_recordedEvolution` | **decoherence formula:** `Γ i j = ∑ₖₗ W i k U k j · conj(W i l U l j) · ⟨φ_l, φ_k⟩` | Zurek (2003) | | ⏳ |
| `ISM.IsRecording.envMarginal_of_orthonormal` | perfect record ⇒ `Γ = \|W\|² · \|U\|²` (no interference) | Zurek (2003) | | ⏳ |
| `ISM.IsRecording.envMarginal_of_const` | no record ⇒ `Γ = \|W U\|²` (coherent evolution) | standard | | ⏳ |
| `ISM.GenStochasticProcess.recordedAt_isDivisionEvent` | **decoherence creates division events:** a perfect record at `t₁` makes `t₁` a division event, with no one reading it | arXiv:2302.10778 | | ⏳ |
| `ISM.Qubit.decoheredProcess_swap` | after a partial record with overlap `cos θ` at `π/4`, the probability of a swap at `π/2` is `(1 + cos θ)/2` | — | | ⏳ |
| `ISM.Qubit.decoheredProcess_isDivisionEvent_iff` | `π/4` is a division event iff the record is perfect (`cos θ = 0`) | — | | ⏳ |
| `ISM.GenStochasticProcess.ofUnitary_kronecker` | independent unitaries `U(t) ⊗ V(t)` give the product process | standard | | ⏳ |
| `ISM.GenStochasticProcess.prod_isDivisionEvent` | a time that divides two independent processes divides their product | — | | ⏳ |
| `ISM.envMarginal_one_kronecker_mul` | **no signalling:** a unitary on the second system does not change the first system's transition probabilities | Ghirardi–Rimini–Weber (1980); arXiv:2402.16935 | local *unitaries* only; local measurements are not yet covered | ⏳ |
| `ISM.BellPair.not_product` | after the Bell preparation the two qubits' joint distribution is not a product | standard | | ⏳ |
| `ISM.BellPair.coherent` | without a division event, the qubits still agree after local Hadamards on both | Nielsen–Chuang | | ⏳ |
| `ISM.BellPair.decohered_of_isRecording` | a perfect record right after the preparation makes the same local Hadamards give the uniform distribution | arXiv:2302.10778 §3.9 | | ⏳ |
| `ISM.Qubit.measuredProcess_isDivisionEvent` | measuring the qubit at `π/4` makes `π/4` a division event (compare `not_isDivisionEvent_pi_div_four`) | — | | ⏳ |

## References

Each bibliographic reference must be checked by a human against the actual paper (that it
exists, and that it says what we cite it for).

| Reference | Cited in | Status |
|---|---|---|
| Barandes, *The Stochastic-Quantum Correspondence*, arXiv:2302.10778 | code, README, book | ⏳ |
| Barandes, *The Stochastic-Quantum Theorem*, arXiv:2309.03085 | code, README, book | ⏳ |
| Barandes, *Quantum Systems as Indivisible Stochastic Processes*, arXiv:2507.21192 (journal: Stud. Hist. Phil. Sci., 2026?) | README, book | ⏳ |
| Zurek, *Decoherence, einselection, and the quantum origins of the classical*, Rev. Mod. Phys. 75, 715 (2003) | code, book | ⏳ |
| Barandes, *New Prospects for a Causally Local Formulation of Quantum Theory*, arXiv:2402.16935 | code, book | ⏳ |
| Ghirardi, Rimini, Weber, Lett. Nuovo Cimento 27, 293 (1980) (no signalling) | code, book | ⏳ |
| Nielsen and Chuang, *Quantum Computation and Quantum Information* (Cambridge, 2000) | code, book | ⏳ |
| arXiv:2602.01043, 2603.27369, 2608.04354, 2601.18720 (Calvo); Horsocrates (Rocq) | ROADMAP | ⏳ |
