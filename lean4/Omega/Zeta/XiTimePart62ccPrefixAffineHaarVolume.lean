import Omega.Zeta.XiTimePart62ccEventwordFreeAffineSubmonoid

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part62cc-prefix-affine-haar-volume`. -/
theorem paper_xi_time_part62cc_prefix_affine_haar_volume
    (D : xi_time_part62cc_eventword_free_affine_submonoid_data) [Fintype D.Event] (n : ℕ) :
    Fintype.card (Fin n → D.Event) = Fintype.card D.Event ^ n ∧
      (D.base : ℚ) ^ (2 * n) * (1 / (D.base : ℚ) ^ (2 * n)) = 1 := by
  constructor
  · rw [Fintype.card_fun, Fintype.card_fin]
  · have hbase_ne : (D.base : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt D.base_pos)
    exact mul_one_div_cancel (pow_ne_zero (2 * n) hbase_ne)

end Omega.Zeta
