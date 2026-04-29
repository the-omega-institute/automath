import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-node-coalescence-quartic-discriminant-law`. -/
theorem paper_conclusion_node_coalescence_quartic_discriminant_law (clusterSize : ℕ) :
    4 * Nat.choose clusterSize 2 = 2 * clusterSize * (clusterSize - 1) := by
  rw [Nat.choose_two_right]
  have hpair_even : 2 ∣ clusterSize * (clusterSize - 1) :=
    (Nat.even_mul_pred_self clusterSize).two_dvd
  rw [← Nat.mul_div_assoc 4 hpair_even]
  rw [show 4 * (clusterSize * (clusterSize - 1)) =
      2 * (2 * (clusterSize * (clusterSize - 1))) by ring]
  rw [Nat.mul_div_right _ (by norm_num : 0 < 2)]
  ring

end Omega.Conclusion
