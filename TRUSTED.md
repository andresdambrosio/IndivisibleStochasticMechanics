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

## Main theorems

| Declaration | Statement in words | Source | Notes | Status |
|---|---|---|---|---|
| `ISM.IsUnistochastic.mem_colStochastic` | every unistochastic matrix is stochastic | standard | | ⏳ |
| `ISM.Qubit.process_Γ` | for the qubit, `Γ(t) = [[cos²t, sin²t], [sin²t, cos²t]]` | — | | ⏳ |
| `ISM.Qubit.process_isIndivisible` | the qubit's process is indivisible | — | | ⏳ |

## References

Each bibliographic reference must be checked by a human against the actual paper (that it
exists, and that it says what we cite it for).

| Reference | Cited in | Status |
|---|---|---|
| Barandes, *The Stochastic-Quantum Correspondence*, arXiv:2302.10778 | code, README, book | ⏳ |
| Barandes, *The Stochastic-Quantum Theorem*, arXiv:2309.03085 | code, README, book | ⏳ |
| Barandes, *Quantum Systems as Indivisible Stochastic Processes*, arXiv:2507.21192 (journal: Stud. Hist. Phil. Sci., 2026?) | README, book | ⏳ |
| arXiv:2602.01043, 2603.27369, 2608.04354, 2601.18720 (Calvo); Horsocrates (Rocq) | ROADMAP | ⏳ |
