import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedWindow6B3C3RootcloudIsotropicDesign
import Omega.GU.Window6B3C3EuclideanCubature

namespace Omega.Zeta

/-- The explicit window-`6` `B₃` root packet reused in the radial design audit. -/
def xi_time_part9r_window6_radial_spherical_3design_b3_root_packet : List Omega.GU.Weight :=
  Omega.DerivedConsequences.derived_window6_b3c3_rootcloud_isotropic_design_b3_roots

/-- The normalized second moment of the first coordinate after radial projection to the unit
sphere: two axial roots contribute `1`, eight mixed roots contribute `1/2`, and eight roots have
vanishing first coordinate. -/
def xi_time_part9r_window6_radial_spherical_3design_first_coordinate_second_moment : ℚ :=
  ((2 : ℚ) * 1 + 8 * (1 / 2 : ℚ)) / 18

/-- The normalized fourth moment of the first coordinate after radial projection to the unit
sphere: the same two axial roots contribute `1`, while the eight mixed roots contribute `1/4`. -/
def xi_time_part9r_window6_radial_spherical_3design_first_coordinate_fourth_moment : ℚ :=
  ((2 : ℚ) * 1 + 8 * (1 / 4 : ℚ)) / 18

/-- Concrete radial spherical-design package for the window-`6` `B₃` packet. -/
def xi_time_part9r_window6_radial_spherical_3design_statement : Prop :=
  xi_time_part9r_window6_radial_spherical_3design_b3_root_packet.length = 18 ∧
    (∀ z : ℤ, z + (-z) = 0) ∧
    (∀ z : ℤ, z ^ 3 + (-z) ^ 3 = 0) ∧
    xi_time_part9r_window6_radial_spherical_3design_first_coordinate_second_moment = 1 / 3 ∧
    xi_time_part9r_window6_radial_spherical_3design_first_coordinate_fourth_moment = 2 / 9 ∧
    xi_time_part9r_window6_radial_spherical_3design_first_coordinate_fourth_moment ≠ 1 / 5

/-- Paper label: `thm:xi-time-part9r-window6-radial-spherical-3design`. The explicit window-`6`
`B₃` root packet has `18` roots, antipodal symmetry kills the odd moments, the radially projected
first-coordinate second moment matches the spherical `3`-design benchmark `1/3`, and the fourth
moment `2/9` misses the spherical `4`-design benchmark `1/5`. -/
theorem paper_xi_time_part9r_window6_radial_spherical_3design :
    xi_time_part9r_window6_radial_spherical_3design_statement := by
  rcases Omega.GU.paper_window6_b3_degree3_euclidean_cubature with ⟨hodd1, hodd3, _, _, _⟩
  refine ⟨?_, hodd1, hodd3, ?_, ?_, ?_⟩
  · unfold xi_time_part9r_window6_radial_spherical_3design_b3_root_packet
    native_decide
  · norm_num [xi_time_part9r_window6_radial_spherical_3design_first_coordinate_second_moment]
  · norm_num [xi_time_part9r_window6_radial_spherical_3design_first_coordinate_fourth_moment]
  · norm_num [xi_time_part9r_window6_radial_spherical_3design_first_coordinate_fourth_moment]
