import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `cor:pom-collision-moments-replica-fusion-space`. -/
theorem paper_pom_collision_moments_replica_fusion_space {ι : Type} [Fintype ι] (q : ℕ)
    (d dimH : ι → ℕ) (hdim : ∀ x, dimH x = d x) :
    (∑ x, (dimH x) ^ q) = ∑ x, (d x) ^ q := by
  simp [hdim]

end Omega.POM
