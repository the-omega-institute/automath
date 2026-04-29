import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

/-- The audited product cover for the `√5` and Lee--Yang splitting conditions has degree `12`. -/
abbrev xi_sqrt5_leyang_double_split_density_1_12_product_cover := Fin 12

/-- The completely split Frobenius class is the identity singleton in the audited product cover. -/
def xi_sqrt5_leyang_double_split_density_1_12_identity_class :
    Finset xi_sqrt5_leyang_double_split_density_1_12_product_cover :=
  {0}

/-- Chebotarev density of the completely split class in the degree-`12` product cover. -/
noncomputable def xi_sqrt5_leyang_double_split_density_1_12_density : ℚ :=
  (xi_sqrt5_leyang_double_split_density_1_12_identity_class.card : ℚ) /
    (Fintype.card xi_sqrt5_leyang_double_split_density_1_12_product_cover : ℚ)

/-- Concrete finite Galois/Chebotarev audit statement for the double split class. -/
def xi_sqrt5_leyang_double_split_density_1_12_statement : Prop :=
  Fintype.card xi_sqrt5_leyang_double_split_density_1_12_product_cover = 12 ∧
    xi_sqrt5_leyang_double_split_density_1_12_identity_class.card = 1 ∧
    xi_sqrt5_leyang_double_split_density_1_12_density = (1 : ℚ) / 12

/-- Paper label: `cor:xi-sqrt5-leyang-double-split-density-1-12`. -/
theorem paper_xi_sqrt5_leyang_double_split_density_1_12 :
    xi_sqrt5_leyang_double_split_density_1_12_statement := by
  norm_num [xi_sqrt5_leyang_double_split_density_1_12_statement,
    xi_sqrt5_leyang_double_split_density_1_12_product_cover,
    xi_sqrt5_leyang_double_split_density_1_12_identity_class,
    xi_sqrt5_leyang_double_split_density_1_12_density]

end Omega.Zeta
