import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9zj-output-bucket-full-tower-sufficiency`. -/
theorem paper_xi_time_part9zj_output_bucket_full_tower_sufficiency
    (sameBuckets sameProjectiveBridge sameMomentTower : Prop)
    (hProjective : sameBuckets → sameProjectiveBridge)
    (hTower : sameBuckets → sameMomentTower) :
    sameBuckets → sameProjectiveBridge ∧ sameMomentTower := by
  intro hBuckets
  exact ⟨hProjective hBuckets, hTower hBuckets⟩

end Omega.Zeta
