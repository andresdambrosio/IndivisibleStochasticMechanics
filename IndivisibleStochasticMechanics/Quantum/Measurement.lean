/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Quantum.Dilation

/-!
# Measurement: the Born rule from configuration statistics

In textbook quantum mechanics, measuring an observable with orthonormal eigenvectors `v a`
on a state `ψ` gives outcome `a` with probability `|⟨v a, ψ⟩|²`. This is the Born rule,
and it is a **postulate**.

In Indivisible Stochastic Mechanics only configurations are physical. A measurement is a
physical interaction between the system and an **apparatus** whose pointer has a
configuration: `none` (ready) or `some a` (it shows outcome `a`). The probability of an
outcome is simply the probability of a pointer configuration, an ordinary transition
probability of the composite system.

We show that an *ideal (von Neumann) measurement* interaction exists for every
observable, and that the resulting pointer-configuration probabilities **are** the Born
probabilities. In this picture the Born rule for arbitrary observables is a theorem about
configurations rather than a postulate.

## Main definitions

* `ISM.IsIdealMeasurement V M`: `M` is a unitary on system ⊗ pointer that, with the
  pointer ready, maps `|j⟩ ⊗ |ready⟩ ↦ ∑ a, (P a |j⟩) ⊗ |a⟩`, where `P a = |v a⟩⟨v a|`
  and the vectors `v a` are the columns of `V`.

## Main results

* `ISM.exists_isIdealMeasurement`: every observable (orthonormal eigenbasis) admits an
  ideal measurement interaction.
* `ISM.IsIdealMeasurement.pointer_prob`: the Born rule for an arbitrary state `ψ`.
* `ISM.IsIdealMeasurement.prob_after_evolution`: the Born rule in stochastic language. The
  system starts in configuration `j` and the pointer is ready. The system evolves by `U`
  and is then measured. The probability that the pointer configuration ends at `a` is
  `|⟨v a| U |j⟩|²`.

## References

* J. A. Barandes, *The Stochastic-Quantum Correspondence*, arXiv:2302.10778
  (measurement and the Born rule).
* J. von Neumann, *Mathematical Foundations of Quantum Mechanics* (1932), ch. VI.
-/

@[expose] public section

open Matrix Kronecker

namespace ISM

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `M` is an ideal measurement of the observable whose eigenvectors are the columns of `V`:
a unitary on system ⊗ pointer such that, with the pointer ready (`none`),
`M (|j⟩ ⊗ |ready⟩) = ∑ a, V j a* · |v a⟩ ⊗ |a⟩`. -/
def IsIdealMeasurement (V : Matrix n n ℂ) (M : Matrix (n × Option n) (n × Option n) ℂ) :
    Prop :=
  M ∈ unitaryGroup (n × Option n) ℂ ∧
    ∀ i j, M (i, none) (j, none) = 0 ∧ ∀ a, M (i, some a) (j, none) = V i a * star (V j a)

/-- The columns `M (·, ·) (j, none)` of an ideal measurement, as vectors. -/
noncomputable def measurementVec (V : Matrix n n ℂ) (c : n × Option n) :
    EuclideanSpace ℂ (n × Option n) :=
  WithLp.toLp 2 fun x => x.2.elim 0 fun a => V x.1 a * star (V c.1 a)

theorem measurementVec_orthonormal {V : Matrix n n ℂ} (hV : V ∈ unitaryGroup n ℂ) :
    Orthonormal ℂ ({c : n × Option n | c.2 = none}.domRestrict (measurementVec V)) := by
  rw [orthonormal_iff_ite]
  rintro ⟨⟨j, _⟩, hj⟩ ⟨⟨k, _⟩, hk⟩
  simp only [Set.mem_ofPred_eq] at hj hk
  subst hj hk
  simp only [Set.domRestrict_apply, PiLp.inner_apply]
  simp [measurementVec, Fintype.sum_prod_type]
  have hcol : ∀ i, ∑ x, V x i * (starRingEnd ℂ) (V x i) = 1 := fun i => by
    have h := congrFun (congrFun (mem_unitaryGroup_iff'.mp hV) i) i
    simpa [Matrix.mul_apply, mul_comm] using h
  have hrow := congrFun (congrFun (mem_unitaryGroup_iff.mp hV) j) k
  simp only [Matrix.mul_apply, star_apply, Complex.star_def] at hrow
  rw [Matrix.one_apply] at hrow
  rw [Finset.sum_comm, ← hrow]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc ∑ x, V x i * (starRingEnd ℂ) (V k i) * ((starRingEnd ℂ) (V x i) * V j i)
      = V j i * (starRingEnd ℂ) (V k i) * ∑ x, V x i * (starRingEnd ℂ) (V x i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ = V j i * (starRingEnd ℂ) (V k i) := by rw [hcol, mul_one]

/-- Every observable admits an ideal measurement interaction. -/
theorem exists_isIdealMeasurement {V : Matrix n n ℂ} (hV : V ∈ unitaryGroup n ℂ) :
    ∃ M, IsIdealMeasurement V M := by
  obtain ⟨M, hM, hMv⟩ := exists_mem_unitaryGroup_of_orthonormal (measurementVec_orthonormal hV)
  refine ⟨M, hM, fun i j => ⟨?_, fun a => ?_⟩⟩ <;>
    simp [hMv (j, none) rfl, measurementVec]

/-- The composite state "system in `ψ`, pointer ready". -/
def readyState (ψ : n → ℂ) (x : n × Option n) : ℂ :=
  if x.2 = none then ψ x.1 else 0

/-- **Born rule from configuration statistics.** For a system in state `ψ` and a ready
pointer, after an ideal measurement the probability that the pointer shows `a` equals
`|⟨v a, ψ⟩|²`. -/
theorem IsIdealMeasurement.pointer_prob {V : Matrix n n ℂ}
    {M : Matrix (n × Option n) (n × Option n) ℂ} (hV : V ∈ unitaryGroup n ℂ)
    (hM : IsIdealMeasurement V M) (ψ : n → ℂ) (a : n) :
    ∑ i, ‖(M *ᵥ readyState ψ) (i, some a)‖ ^ 2 = ‖(Vᴴ *ᵥ ψ) a‖ ^ 2 := by
  have h : ∀ i, (M *ᵥ readyState ψ) (i, some a) = V i a * (Vᴴ *ᵥ ψ) a := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_option, readyState]
    simp [(hM.2 _ _).2, Finset.mul_sum, conjTranspose_apply, mul_assoc]
  simp_rw [h, norm_mul, mul_pow]
  rw [← Finset.sum_mul, unitary_col_normSq_sum hV a, one_mul]

/-- **The Born rule in stochastic language.** The system starts in configuration `j` and the
pointer is ready. The system evolves by the unitary `U`, and is then measured. The
probability that the composite system ends with the pointer in configuration `a`,
whatever the system's configuration, is `|⟨v a| U |j⟩|²`. -/
theorem IsIdealMeasurement.prob_after_evolution {V U : Matrix n n ℂ}
    {M : Matrix (n × Option n) (n × Option n) ℂ} (hV : V ∈ unitaryGroup n ℂ)
    (hM : IsIdealMeasurement V M) (j a : n) :
    ∑ i, ‖(M * (U ⊗ₖ (1 : Matrix (Option n) (Option n) ℂ))) (i, some a) (j, none)‖ ^ 2 =
      ‖(Vᴴ * U) a j‖ ^ 2 := by
  have h : ∀ i, (M * (U ⊗ₖ (1 : Matrix (Option n) (Option n) ℂ))) (i, some a) (j, none) =
      (M *ᵥ readyState fun k => U k j) (i, some a) := by
    intro i
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, readyState]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hx <;> simp [hx, Matrix.one_apply]
  simp_rw [h]
  rw [hM.pointer_prob hV]
  simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]

end ISM
