import Mathlib.Tactic
import Omega.Conclusion.M2Level3XiDelta0Order6Cycletypes

namespace Omega.Conclusion

/-- Multiplicities of the order-`6` local factors `(T - 1)`, `(T + 1)`, `(T^2 + T + 1)`, and
`(T^2 - T + 1)` on the Klingen fiber. -/
def conclusion_m2_level3_xi_delta0_order6_parabolic_spectrum_klingen_weights :
    ℕ × ℕ × ℕ × ℕ :=
  conclusion_m2_level3_xi_delta0_order6_cycletypes_klingen_cycle_counts

/-- Multiplicities of the order-`6` local factors `(T - 1)`, `(T + 1)`, `(T^2 + T + 1)`, and
`(T^2 - T + 1)` on the Siegel fiber. -/
def conclusion_m2_level3_xi_delta0_order6_parabolic_spectrum_siegel_weights :
    ℕ × ℕ × ℕ × ℕ :=
  conclusion_m2_level3_xi_delta0_order6_cycletypes_siegel_cycle_counts

/-- Multiplicities of the order-`6` local factors `(T - 1)`, `(T + 1)`, `(T^2 + T + 1)`, and
`(T^2 - T + 1)` on the full flag fiber. -/
def conclusion_m2_level3_xi_delta0_order6_parabolic_spectrum_flag_weights :
    ℕ × ℕ × ℕ × ℕ :=
  conclusion_m2_level3_xi_delta0_order6_cycletypes_flag_cycle_counts

/-- Paper label: `cor:conclusion-m2-level3-xi-delta0-order6-parabolic-spectrum`. The audited
order-`6` cycle data for `Xi ∩ Delta0` directly record the multiplicities of the four parabolic
local factors `(T - 1)`, `(T + 1)`, `(T^2 + T + 1)`, and `(T^2 - T + 1)` on the Klingen, Siegel,
and full-flag fibers. -/
theorem paper_conclusion_m2_level3_xi_delta0_order6_parabolic_spectrum :
    conclusion_m2_level3_xi_delta0_order6_parabolic_spectrum_klingen_weights = (5, 4, 1, 4) ∧
      conclusion_m2_level3_xi_delta0_order6_parabolic_spectrum_siegel_weights = (4, 0, 4, 4) ∧
      conclusion_m2_level3_xi_delta0_order6_parabolic_spectrum_flag_weights = (8, 4, 8, 20) ∧
      Fintype.card conclusion_m2_level3_xi_delta0_order6_cycletypes_klingen_fiber =
        5 + 2 * 4 + 3 * 1 + 6 * 4 ∧
      Fintype.card conclusion_m2_level3_xi_delta0_order6_cycletypes_siegel_fiber =
        4 + 2 * 0 + 3 * 4 + 6 * 4 ∧
      Fintype.card conclusion_m2_level3_xi_delta0_order6_cycletypes_flag_fiber =
        8 + 2 * 4 + 3 * 8 + 6 * 20 := by
  have hcycle := paper_conclusion_m2_level3_xi_delta0_order6_cycletypes ⟨()⟩
  rcases hcycle with ⟨hkCard, hsCard, hfCard, hk, hs, hf⟩
  refine ⟨hk, hs, hf, ?_, ?_, ?_⟩
  · norm_num at hkCard ⊢
  · norm_num at hsCard ⊢
  · norm_num at hfCard ⊢

end Omega.Conclusion
