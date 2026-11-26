/-
Copyright (c) 2026 Indivisible Stochastic Mechanics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IndivisibleStochasticMechanics.Examples.Qubit
public import IndivisibleStochasticMechanics.Quantum.Collapse

/-!
# Measuring the qubit creates a division event

The qubit of `ISM.Qubit` evolves under `H = σₓ`, and `π/4` is **not** a division event of its
process (`ISM.Qubit.not_isDivisionEvent_pi_div_four`). If an apparatus measures the qubit's
configuration at `π/4`, then `π/4` **is** a division event (`measuredProcess_isDivisionEvent`).
The same unitary dynamics gives a divisible or an indivisible history depending on whether a
measurement happens. This is collapse, seen from the stochastic side.
-/

@[expose] public section

open Matrix

namespace ISM.Qubit

/-- An ideal measurement of the configuration of the qubit. -/
noncomputable def configMeasurement :
    Matrix (Fin 2 × Option (Fin 2)) (Fin 2 × Option (Fin 2)) ℂ :=
  (exists_isIdealMeasurement (one_mem (unitaryGroup (Fin 2) ℂ))).choose

/-- `configMeasurement` is an ideal measurement of the configuration. -/
theorem configMeasurement_spec : IsIdealMeasurement 1 configMeasurement :=
  (exists_isIdealMeasurement (one_mem (unitaryGroup (Fin 2) ℂ))).choose_spec

/-- The qubit process with its configuration measured at `π/4`. -/
noncomputable def measuredProcess : GenStochasticProcess (Fin 2) :=
  GenStochasticProcess.measuredAt U U_mem_unitaryGroup U_zero configMeasurement
    configMeasurement_spec.1 (Real.pi / 4) (by positivity)

/-- With a measurement at `π/4`, `π/4` becomes a division event. -/
theorem measuredProcess_isDivisionEvent : measuredProcess.IsDivisionEvent (Real.pi / 4) :=
  GenStochasticProcess.measuredAt_isDivisionEvent configMeasurement_spec

end ISM.Qubit
