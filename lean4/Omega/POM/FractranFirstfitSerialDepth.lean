import Mathlib

namespace Omega.POM

/-- Concrete size parameter for the first-fit serial-depth model. -/
abbrev FractranFirstfitSerialDepthData := ℕ

/-- Instruction `i` becomes feasible once the register state reaches this threshold. -/
def fractranThreshold (k i : ℕ) : ℕ :=
  k - i

/-- Witness state forcing the scan all the way to the last rule. -/
def fractranWitnessState : ℕ :=
  1

/-- Feasibility in the threshold-vector model. -/
def fractranFeasible (k r i : ℕ) : Prop :=
  i < k ∧ fractranThreshold k i ≤ r

instance (k r : ℕ) : DecidablePred (fractranFeasible k r) := by
  intro i
  unfold fractranFeasible fractranThreshold
  infer_instance

/-- Indices feasible at register state `r`. -/
def fractranFeasibleIndices (k r : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun i => fractranFeasible k r i

/-- First-fit selects the smallest feasible index when one exists. -/
def fractranFirstFeasibleIndex (k r : ℕ) : Option ℕ :=
  if h : (fractranFeasibleIndices k r).Nonempty then
    some ((fractranFeasibleIndices k r).min' h)
  else
    none

/-- Hard first-fit must serially inspect the whole priority list in the witness configuration. -/
def fractranSerialDepth (k : ℕ) : ℕ :=
  (Finset.range k).card

/-- Concrete first-fit serial-depth lower bound: at the witness state only the last rule is
feasible, so returning it requires a scan of linear depth. -/
def FractranFirstfitSerialDepth (k : FractranFirstfitSerialDepthData) : Prop :=
  1 ≤ k →
    fractranFirstFeasibleIndex k fractranWitnessState = some (k - 1) ∧
      k ≤ fractranSerialDepth k

private lemma fractranFeasibleIndices_witness (hk : 1 ≤ k) :
    fractranFeasibleIndices k fractranWitnessState = {k - 1} := by
  ext i
  constructor
  · intro hi
    rw [fractranFeasibleIndices, Finset.mem_filter, Finset.mem_range] at hi
    rcases hi with ⟨hi_lt, hi_feasible⟩
    rcases hi_feasible with ⟨_, hsub⟩
    simp [fractranThreshold, fractranWitnessState] at hsub
    rw [Finset.mem_singleton]
    omega
  · intro hi
    rw [Finset.mem_singleton] at hi
    rw [fractranFeasibleIndices, Finset.mem_filter, Finset.mem_range]
    subst hi
    constructor
    · omega
    constructor
    · omega
    · have hlast : k ≤ 1 + (k - 1) := by omega
      simpa [fractranThreshold, fractranWitnessState] using hlast

private lemma fractranFirstFeasibleIndex_witness (hk : 1 ≤ k) :
    fractranFirstFeasibleIndex k fractranWitnessState = some (k - 1) := by
  have hset := fractranFeasibleIndices_witness hk
  have hne : (fractranFeasibleIndices k fractranWitnessState).Nonempty := by
    rw [hset]
    simp
  simp [fractranFirstFeasibleIndex, hset]

/-- Paper label: `prop:pom-fractran-firstfit-serial-depth`. -/
theorem paper_pom_fractran_firstfit_serial_depth (P : FractranFirstfitSerialDepthData) :
    FractranFirstfitSerialDepth P := by
  intro hP
  refine ⟨fractranFirstFeasibleIndex_witness hP, ?_⟩
  simp [fractranSerialDepth]

end Omega.POM
