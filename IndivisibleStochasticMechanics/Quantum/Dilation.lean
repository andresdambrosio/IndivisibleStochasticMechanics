/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Quantum.UnitaryProcess
public import IndivisibleStochasticMechanics.ForMathlib.Matrix.Unitary

/-!
# Unitary dilations: the stochastic → quantum direction

Not every stochastic matrix is unistochastic, so a stochastic process cannot always be
written as `Γ i j = ‖U i j‖²` on the *same* configuration space. It can, however, always be
realized as the **marginal of a unitary evolution on a larger system**: the original
configurations `n` together with an environment `m`, prepared in a fixed state `e₀`.

  `Γ i j = ∑ e, ‖U (i, e) (j, e₀)‖²`

Here `Γ i j` is the probability of finding the system in `i`, *whatever the environment
does*, given that it started in `j`.

## The construction

Take the environment `Option n`, prepared in `none`. For each initial configuration `j`,
define

  `v j = ∑ i, √Γᵢⱼ · |i⟩ ⊗ |some j⟩`,

so the environment records the initial configuration. These vectors are orthonormal
*because* the columns of `Γ` sum to one. Complete them to a unitary matrix `U`.
Marginalizing `‖U‖²` over the environment then returns `Γ`.

## Main results

* `ISM.IsUnitaryDilation.mem_colStochastic`: the marginal of a unitary is stochastic
  (quantum → stochastic, for any environment).
* `ISM.exists_isUnitaryDilation`: every stochastic matrix has a unitary dilation
  (stochastic → quantum).
* `ISM.forall_mem_colStochastic_iff_exists_isUnitaryDilation`: the **stochastic-quantum
  correspondence in finite dimensions**. A family of transition matrices is stochastic
  at every time iff at every time it is the marginal of a unitary evolution of system ⊗
  environment.

## References

* J. A. Barandes, *The Stochastic-Quantum Theorem*, arXiv:2309.03085. Our construction is
  a direct Stinespring-type dilation and need not coincide with the one in the paper.
-/

@[expose] public section

open Matrix

namespace ISM

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- `U` is a *unitary dilation* of `Γ` with environment `m` prepared in `e₀`:
`U` is unitary on system ⊗ environment and `Γ i j = ∑ e, ‖U (i, e) (j, e₀)‖²`. -/
def IsUnitaryDilation (Γ : Matrix n n ℝ) (U : Matrix (n × m) (n × m) ℂ) (e₀ : m) : Prop :=
  U ∈ unitaryGroup (n × m) ℂ ∧ ∀ i j, Γ i j = ∑ e, ‖U (i, e) (j, e₀)‖ ^ 2

/-- Quantum → stochastic: the system marginal of a unitary evolution is stochastic. -/
theorem IsUnitaryDilation.mem_colStochastic {Γ : Matrix n n ℝ}
    {U : Matrix (n × m) (n × m) ℂ} {e₀ : m} (h : IsUnitaryDilation Γ U e₀) :
    Γ ∈ colStochastic ℝ n := by
  obtain ⟨hU, hΓ⟩ := h
  refine mem_colStochastic_iff_sum.mpr ⟨fun i j => ?_, fun j => ?_⟩
  · rw [hΓ]; positivity
  · rw [Finset.sum_congr rfl fun i _ => hΓ i j,
      ← Fintype.sum_prod_type' (fun i e => ‖U (i, e) (j, e₀)‖ ^ 2)]
    exact unitary_col_normSq_sum hU (j, e₀)

/-- The columns used to build the dilation: `v (j, _) = ∑ i, √Γᵢⱼ · |i⟩ ⊗ |some j⟩`. -/
noncomputable def dilationVec (Γ : Matrix n n ℝ) (c : n × Option n) :
    EuclideanSpace ℂ (n × Option n) :=
  WithLp.toLp 2 fun a => if a.2 = some c.1 then (Real.sqrt (Γ a.1 c.1) : ℂ) else 0

/-- The dilation columns with environment `none` are orthonormal, because the columns of a
stochastic matrix sum to one. -/
theorem dilationVec_orthonormal {Γ : Matrix n n ℝ} (hΓ : Γ ∈ colStochastic ℝ n) :
    Orthonormal ℂ ({c : n × Option n | c.2 = none}.domRestrict (dilationVec Γ)) := by
  rw [orthonormal_iff_ite]
  rintro ⟨⟨j, _⟩, hj⟩ ⟨⟨k, _⟩, hk⟩
  simp only [Set.mem_ofPred_eq] at hj hk
  subst hj hk
  simp only [Set.domRestrict_apply, PiLp.inner_apply]
  simp [dilationVec]
  rw [Fintype.sum_prod_type]
  by_cases hjk : j = k
  · subst hjk
    have h := sum_col_of_mem_colStochastic hΓ j
    simp [Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (nonneg_of_mem_colStochastic hΓ)]
    exact_mod_cast h
  · simp [hjk, Ne.symm hjk]

/-- Stochastic → quantum: every stochastic matrix has a unitary dilation, with
environment `Option n` prepared in `none`. -/
theorem exists_isUnitaryDilation {Γ : Matrix n n ℝ} (hΓ : Γ ∈ colStochastic ℝ n) :
    ∃ U : Matrix (n × Option n) (n × Option n) ℂ, IsUnitaryDilation Γ U none := by
  obtain ⟨U, hU, hUv⟩ := exists_mem_unitaryGroup_of_orthonormal (dilationVec_orthonormal hΓ)
  refine ⟨U, hU, fun i j => ?_⟩
  simp only [hUv (j, none) rfl, dilationVec]
  simp only [Fintype.sum_option]
  simp [apply_ite (fun z : ℂ => ‖z‖ ^ 2), Complex.norm_real,
    Real.sq_sqrt (nonneg_of_mem_colStochastic hΓ)]

/-- **The stochastic-quantum correspondence in finite dimensions.**
A family of transition matrices `Γ t` is stochastic at every time `t ≥ 0` if and only if
at every time it is the system marginal of a unitary evolution of system ⊗ environment,
with the environment prepared in a fixed state. -/
theorem forall_mem_colStochastic_iff_exists_isUnitaryDilation (Γ : ℝ → Matrix n n ℝ) :
    (∀ t, 0 ≤ t → Γ t ∈ colStochastic ℝ n) ↔
      ∃ U : ℝ → Matrix (n × Option n) (n × Option n) ℂ,
        ∀ t, 0 ≤ t → IsUnitaryDilation (Γ t) (U t) none := by
  constructor
  · intro h
    choose U hU using fun t : {t : ℝ // 0 ≤ t} => exists_isUnitaryDilation (h t.1 t.2)
    exact ⟨fun t => if ht : 0 ≤ t then U ⟨t, ht⟩ else 1, fun t ht => by simpa [ht] using hU ⟨t, ht⟩⟩
  · rintro ⟨U, hU⟩ t ht
    exact (hU t ht).mem_colStochastic

/-- Every generalized stochastic process is, at each time, the marginal of a unitary
evolution on a larger configuration space. -/
theorem GenStochasticProcess.exists_isUnitaryDilation (P : GenStochasticProcess n) :
    ∃ U : ℝ → Matrix (n × Option n) (n × Option n) ℂ,
      ∀ t, 0 ≤ t → IsUnitaryDilation (P.Γ t) (U t) none :=
  (forall_mem_colStochastic_iff_exists_isUnitaryDilation P.Γ).mp P.stochastic

end ISM
