import Mathlib.Tactic
import Omega.EA.SyncKernelResetWords

namespace Omega.EA

open scoped BigOperators

/-- Uniform-input transition kernel on the 10-state synchronization automaton. -/
def sync10UniformKernel (q q' : Sync10State) : ℚ :=
  ((Finset.univ.filter fun d : Fin 3 => sync10Step q d = q').card : ℚ) / 3

/-- The explicit stationary law of the uniform-input `Sync10` chain in appendix order
`000,001,002,010,100,101,0-12,1-12,01-1,11-1`. -/
def sync10UniformStationaryVector : Sync10State → ℚ
  | .q000 => 7 / 48
  | .q001 => 1 / 6
  | .q002 => 1 / 8
  | .q010 => 1 / 8
  | .q100 => 1 / 6
  | .q101 => 7 / 48
  | .q0m12 => 1 / 24
  | .q1m12 => 1 / 48
  | .q01m1 => 1 / 48
  | .q11m1 => 1 / 24

/-- Left action of a probability vector on the uniform `Sync10` kernel. -/
def sync10UniformLeftAction (v : Sync10State → ℚ) (q' : Sync10State) : ℚ :=
  ∑ q, v q * sync10UniformKernel q q'

/-- The explicit vector is normalized and stationary for the uniform-input `Sync10` chain. -/
def sync10UniformNormalizedStationaryVector : Prop :=
  (∑ q, sync10UniformStationaryVector q = 1) ∧
    ∀ q, sync10UniformLeftAction sync10UniformStationaryVector q = sync10UniformStationaryVector q

/-- Uniform-input stationary law for the 10-state synchronization kernel.
    prop:sync10-uniform-stationary -/
theorem paper_sync10_uniform_stationary : sync10UniformNormalizedStationaryVector := by
  unfold sync10UniformNormalizedStationaryVector sync10UniformLeftAction sync10UniformKernel
  unfold sync10UniformStationaryVector
  native_decide

end Omega.EA
