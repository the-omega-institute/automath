import Mathlib.Tactic
import Omega.GU.So10TwoTorsionCentralCollapseNecessity

namespace Omega.GroupUnification

/-- The connected `Spin(10)` center contributes one `2`-torsion bit. -/
abbrev so10ConnectedCenterTwoTorsionRank : ℕ := 1

/-- Adjoining two residual `ℤ₂` factors restores the missing two central bits. -/
abbrev so10ResidualTwoTorsionBits : ℕ := 2

/-- The repaired `Spin(10) × (ℤ₂)^2` witness has three central `2`-torsion directions. -/
def so10MinimalDisconnectedRepairCenterRank : ℕ :=
  so10ConnectedCenterTwoTorsionRank + so10ResidualTwoTorsionBits

/-- The same two residual bits force four connected components. -/
def so10MinimalDisconnectedRepairComponentCount : ℕ :=
  2 ^ so10ResidualTwoTorsionBits

/-- Any `so(10)`-type envelope retaining three audited central `2`-torsion directions must have
at least four connected components, modeled here by the residual `2`-rank. -/
def so10MinimalDisconnectedRepairLowerBound (D : Omega.GU.So10TwoTorsionCentralCollapseData) :
    Prop :=
  4 ≤ 2 ^ (D.auditCentralRank - D.connectedCentralTwoTorsionRank)

/-- Paper-facing arithmetic package for the minimal disconnected repair. -/
def so10TwoTorsionMinimalDisconnectedRepairStatement : Prop :=
  so10MinimalDisconnectedRepairCenterRank = 3 ∧
    so10MinimalDisconnectedRepairComponentCount = 4 ∧
    ∀ D : Omega.GU.So10TwoTorsionCentralCollapseData,
      so10MinimalDisconnectedRepairLowerBound D

/-- Paper label: `cor:so10-2torsion-minimal-disconnected-repair`. -/
def paper_so10_2torsion_minimal_disconnected_repair : Prop :=
  so10TwoTorsionMinimalDisconnectedRepairStatement

theorem paper_so10_2torsion_minimal_disconnected_repair_verified :
    paper_so10_2torsion_minimal_disconnected_repair := by
  unfold paper_so10_2torsion_minimal_disconnected_repair
    so10TwoTorsionMinimalDisconnectedRepairStatement
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro D
  unfold so10MinimalDisconnectedRepairLowerBound
  have hdrop := (Omega.GU.paper_so10_2torsion_central_collapse_necessity D).2
  have hpow : 2 ^ 2 ≤ 2 ^ (D.auditCentralRank - D.connectedCentralTwoTorsionRank) := by
    exact Nat.pow_le_pow_right (by omega) hdrop
  simpa using hpow

end Omega.GroupUnification
