import Mathlib.Tactic
import Omega.GU.Window6B3C3AdjointSecondMomentIsotropy
import Omega.Zeta.XiWindow6C3QuadraticEnergyEquipartition

namespace Omega.DerivedConsequences

/-- The concrete `B₃` root cloud used by the derived isotropic-design wrapper:
the six axial roots `± e_i` together with the twelve mixed roots `± e_i ± e_j`. -/
def derived_window6_b3c3_rootcloud_isotropic_design_b3_roots : List Omega.GU.Weight :=
  [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1), (1, 1, 0), (1, -1, 0),
    (-1, 1, 0), (-1, -1, 0), (1, 0, 1), (1, 0, -1), (-1, 0, 1), (-1, 0, -1), (0, 1, 1),
    (0, 1, -1), (0, -1, 1), (0, -1, -1)]

/-- The concrete `C₃` root cloud used by the derived isotropic-design wrapper:
the six axial roots `± 2 e_i` together with the same twelve mixed roots `± e_i ± e_j`. -/
def derived_window6_b3c3_rootcloud_isotropic_design_c3_roots : List Omega.GU.Weight :=
  [(2, 0, 0), (-2, 0, 0), (0, 2, 0), (0, -2, 0), (0, 0, 2), (0, 0, -2), (1, 1, 0), (1, -1, 0),
    (-1, 1, 0), (-1, -1, 0), (1, 0, 1), (1, 0, -1), (-1, 0, 1), (-1, 0, -1), (0, 1, 1),
    (0, 1, -1), (0, -1, 1), (0, -1, -1)]

/-- Coordinate-wise sum of a concrete root cloud. -/
def derived_window6_b3c3_rootcloud_isotropic_design_sum_weights
    (roots : List Omega.GU.Weight) : Omega.GU.Weight :=
  roots.foldl
    (fun acc v => (acc.1 + v.1, acc.2.1 + v.2.1, acc.2.2 + v.2.2))
    (0, 0, 0)

/-- The `B₃` root cloud has vanishing first moment by pairing opposite roots. -/
def derived_window6_b3c3_rootcloud_isotropic_design_b3_first_moment_zero : Prop :=
  derived_window6_b3c3_rootcloud_isotropic_design_sum_weights
      derived_window6_b3c3_rootcloud_isotropic_design_b3_roots =
    (0, 0, 0)

/-- The `C₃` root cloud has vanishing first moment by pairing opposite roots. -/
def derived_window6_b3c3_rootcloud_isotropic_design_c3_first_moment_zero : Prop :=
  derived_window6_b3c3_rootcloud_isotropic_design_sum_weights
      derived_window6_b3c3_rootcloud_isotropic_design_c3_roots =
    (0, 0, 0)

/-- Paper label: `thm:derived-window6-b3c3-rootcloud-isotropic-design`. The concrete `B₃/C₃`
root clouds are centrally symmetric, the `B₃` second moment is the existing audited `10 I₃`
identity, and the `C₃` side is the existing quadratic equipartition theorem. -/
theorem paper_derived_window6_b3c3_rootcloud_isotropic_design :
    derived_window6_b3c3_rootcloud_isotropic_design_b3_first_moment_zero ∧
      derived_window6_b3c3_rootcloud_isotropic_design_c3_first_moment_zero ∧
      (∀ u : Omega.GU.Weight, Omega.GU.b3SecondMoment u = 10 * Omega.GU.weightNormSq u) ∧
      Omega.Zeta.XiWindow6C3QuadraticEnergyEquipartitionStatement := by
  refine ⟨?_, ?_, Omega.GU.paper_window6_b3c3_adjoint_second_moment_isotropy.1,
    Omega.Zeta.paper_xi_window6_c3_quadratic_energy_equipartition⟩
  · unfold derived_window6_b3c3_rootcloud_isotropic_design_b3_first_moment_zero
      derived_window6_b3c3_rootcloud_isotropic_design_sum_weights
      derived_window6_b3c3_rootcloud_isotropic_design_b3_roots
    native_decide
  · unfold derived_window6_b3c3_rootcloud_isotropic_design_c3_first_moment_zero
      derived_window6_b3c3_rootcloud_isotropic_design_sum_weights
      derived_window6_b3c3_rootcloud_isotropic_design_c3_roots
    native_decide

end Omega.DerivedConsequences
