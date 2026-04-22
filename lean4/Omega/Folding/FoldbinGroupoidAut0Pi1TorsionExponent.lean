import Mathlib.Tactic
import Omega.Folding.FoldbinGroupoidAut0PuProduct

namespace Omega.Folding

/-- The cyclic orders contributed by the connected `PU(d)` factors to the product fundamental
group in the audited foldbin model. -/
def foldbin_groupoid_aut0_pi1_torsion_exponent_cyclic_orders : List ℕ :=
  List.replicate (foldbin_groupoid_aut0_pu_product_connected_factor_count 2) 2 ++
    List.replicate (foldbin_groupoid_aut0_pu_product_connected_factor_count 3) 3 ++
      List.replicate (foldbin_groupoid_aut0_pu_product_connected_factor_count 4) 4

/-- The torsion exponent of the audited product fundamental group, computed as a finite `lcm`
fold over the cyclic factor orders. -/
def foldbin_groupoid_aut0_pi1_torsion_exponent_value : ℕ :=
  foldbin_groupoid_aut0_pi1_torsion_exponent_cyclic_orders.foldl Nat.lcm 1

/-- Concrete package for the foldbin identity-component fundamental-group torsion data coming
from the audited `PU(d)` product decomposition. -/
def foldbin_groupoid_aut0_pi1_torsion_exponent_statement : Prop :=
  foldbin_groupoid_aut0_pi1_torsion_exponent_cyclic_orders =
      List.replicate 8 2 ++ List.replicate 4 3 ++ List.replicate 9 4 ∧
    foldbin_groupoid_aut0_pi1_torsion_exponent_cyclic_orders.length =
      foldbin_groupoid_aut0_pu_product_total_connected_factor_count ∧
    foldbin_groupoid_aut0_pi1_torsion_exponent_value = 12

/-- Paper label: `prop:foldbin-groupoid-aut0-pi1-torsion-exponent`. -/
theorem paper_foldbin_groupoid_aut0_pi1_torsion_exponent :
    foldbin_groupoid_aut0_pi1_torsion_exponent_statement := by
  rcases paper_foldbin_groupoid_aut0_pu_product with
    ⟨_, h2, h3, h4, _, _, htotal, _, _, _, _, _, _⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [foldbin_groupoid_aut0_pi1_torsion_exponent_cyclic_orders, h2, h3, h4]
  · simp [foldbin_groupoid_aut0_pi1_torsion_exponent_cyclic_orders, h2, h3, h4, htotal]
  · simpa [foldbin_groupoid_aut0_pi1_torsion_exponent_value,
      foldbin_groupoid_aut0_pi1_torsion_exponent_cyclic_orders, h2, h3, h4] using
      (show
        (List.foldl Nat.lcm 1
          (List.replicate 8 2 ++ List.replicate 4 3 ++ List.replicate 9 4)) = 12 by
        native_decide)

end Omega.Folding
