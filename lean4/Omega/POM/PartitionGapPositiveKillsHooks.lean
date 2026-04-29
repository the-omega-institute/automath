import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-partition-gap-positive-kills-hooks`. -/
theorem paper_pom_partition_gap_positive_kills_hooks (partitionGap : ℝ) {Hook : Type*}
    (channelNonzero : Hook → Prop) (hgap : 0 < partitionGap)
    (hclosed : ∀ lam : Hook, channelNonzero lam → partitionGap = 0) :
    ∀ lam : Hook, ¬ channelNonzero lam := by
  intro lam hlam
  have hzero : partitionGap = 0 := hclosed lam hlam
  linarith

end Omega.POM
