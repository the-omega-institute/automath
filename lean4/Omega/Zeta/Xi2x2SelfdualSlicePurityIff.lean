import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete slice-purity discriminant for the self-dual `2 × 2` bridge: no off-slice tower is
visible exactly when the coupling is diagonal and the discriminant is nonpositive. -/
def xi_2x2_selfdual_slice_purity_iff_slicePure (a b L : ℝ) : Prop :=
  b = 0 ∧ L ≤ 4 * a ^ 2

/-- Concrete existence criterion for an off-slice root tower in the same `2 × 2` model. -/
def xi_2x2_selfdual_slice_purity_iff_offsliceRootTower (a b L : ℝ) : Prop :=
  b ≠ 0 ∨ 4 * a ^ 2 < L

/-- Paper label: `cor:xi-2x2-selfdual-slice-purity-iff`.

In the self-dual `2 × 2` slice, purity is equivalent to `b = 0` and `L ≤ 4a^2`; its negation is
the explicit off-slice root-tower alternative. -/
theorem paper_xi_2x2_selfdual_slice_purity_iff (a b L : ℝ) (_ha : a ≠ 0) :
    (xi_2x2_selfdual_slice_purity_iff_slicePure a b L ↔ b = 0 ∧ L ≤ 4 * a ^ 2) ∧
    (xi_2x2_selfdual_slice_purity_iff_offsliceRootTower a b L ↔
      ¬ xi_2x2_selfdual_slice_purity_iff_slicePure a b L) := by
  constructor
  · rfl
  · unfold xi_2x2_selfdual_slice_purity_iff_offsliceRootTower
      xi_2x2_selfdual_slice_purity_iff_slicePure
    constructor
    · intro h hpure
      rcases h with hb | hL
      · exact hb hpure.1
      · exact (not_le_of_gt hL) hpure.2
    · intro hnot
      by_cases hb : b = 0
      · right
        exact lt_of_not_ge fun hL => hnot ⟨hb, hL⟩
      · left
        exact hb

end Omega.Zeta
