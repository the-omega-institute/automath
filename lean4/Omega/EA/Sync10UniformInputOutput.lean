import Mathlib.Tactic
import Omega.EA.Sync10UniformStationary

namespace Omega.EA

open scoped BigOperators

/-- The output bit carried by each deterministic edge of the 10-state synchronization transducer. -/
def sync10OutputBit : Sync10State → Fin 3 → Fin 2
  | .q000, _ => 0
  | .q001, _ => 0
  | .q002, ⟨0, _⟩ => 0
  | .q002, ⟨1, _⟩ => 1
  | .q002, ⟨2, _⟩ => 1
  | .q010, ⟨0, _⟩ => 0
  | .q010, ⟨1, _⟩ => 0
  | .q010, ⟨2, _⟩ => 1
  | .q100, _ => 1
  | .q101, _ => 1
  | .q0m12, _ => 0
  | .q1m12, _ => 1
  | .q01m1, _ => 0
  | .q11m1, _ => 1

/-- Exact joint law `P(d,e)` under the verified stationary distribution and uniform input. -/
def sync10JointInputOutputFin (d : Fin 3) (e : Fin 2) : ℚ :=
  ∑ q, sync10UniformStationaryVector q *
    if sync10OutputBit q d = e then (1 / 3 : ℚ) else 0

/-- Nat-indexed wrapper around the exact joint law `P(d,e)`. -/
def sync10JointInputOutput (d e : Nat) : ℚ :=
  if hd : d < 3 then
    if he : e < 2 then
      sync10JointInputOutputFin ⟨d, hd⟩ ⟨e, he⟩
    else
      0
  else
    0

/-- The stationary probability that the output bit equals `1`. -/
def sync10OutputOneProb : ℚ :=
  ∑ d : Fin 3, sync10JointInputOutputFin d 1

/-- The exact conditional law `P(e = 1 | d)`. -/
def sync10ConditionalOutputOne (d : Nat) : ℚ :=
  sync10JointInputOutput d 1 / (1 / 3 : ℚ)

/-- Exact joint input/output law for the 10-state sync kernel under uniform input.
    prop:sync10-uniform-de -/
theorem paper_sync10_uniform_de :
    sync10JointInputOutput 0 0 = 5 / 24 ∧
      sync10JointInputOutput 0 1 = 1 / 8 ∧
        sync10JointInputOutput 1 0 = 1 / 6 ∧
          sync10JointInputOutput 1 1 = 1 / 6 ∧
            sync10JointInputOutput 2 0 = 1 / 8 ∧
              sync10JointInputOutput 2 1 = 5 / 24 ∧
                sync10OutputOneProb = 1 / 2 ∧
                  sync10ConditionalOutputOne 0 = 3 / 8 ∧
                    sync10ConditionalOutputOne 1 = 1 / 2 ∧
                      sync10ConditionalOutputOne 2 = 5 / 8 := by
  unfold sync10JointInputOutput sync10JointInputOutputFin sync10OutputOneProb
  unfold sync10ConditionalOutputOne sync10OutputBit sync10UniformStationaryVector
  native_decide

end Omega.EA
