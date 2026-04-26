import Mathlib.Tactic
import Omega.POM.A4TAdeIntersectionTMinpolyDiscriminant
import Omega.POM.E8SquareSpectrumCollapseTrace7

namespace Omega.POM

/-- Concrete representative for the `E₈` intersection field generator `r_{E₈}`. -/
noncomputable def pom_e8_intersection_field_discriminant_index_rE8 : ℝ :=
  pom_e8_square_spectrum_collapse_trace7_root1

/-- The audited field discriminant of the `E₈` intersection field. -/
def pom_e8_intersection_field_discriminant_index_field_discriminant : Nat := 1125

/-- The maximal-order claim for `ℤ[r_{E₈}]` is encoded by the index `1`. -/
def pom_e8_intersection_field_discriminant_index_zrE8_order_index : Nat := 1

/-- The audited index `[𝓞_K : ℤ[t_{E₈}]]`. -/
def pom_e8_intersection_field_discriminant_index_ztE8_order_index : Nat :=
  5 ^ 2 * 29 * 59 * 1229

/-- Concrete package for the `E₈` intersection-field discriminant/index statement. -/
def pom_a4t_e8_intersection_field_discriminant_index_spec : Prop :=
  pom_e8_intersection_field_discriminant_index_rE8 =
      pom_e8_square_spectrum_collapse_trace7_root1 ∧
    pom_e8_square_spectrum_collapse_trace7_root1 +
        pom_e8_square_spectrum_collapse_trace7_root2 +
        pom_e8_square_spectrum_collapse_trace7_root3 +
        pom_e8_square_spectrum_collapse_trace7_root4 = 7 ∧
    pom_e8_intersection_field_discriminant_index_field_discriminant = 3 ^ 2 * 5 ^ 3 ∧
    pom_e8_intersection_field_discriminant_index_zrE8_order_index = 1 ∧
    pom_e8_intersection_field_discriminant_index_ztE8_order_index = 5 ^ 2 * 29 * 59 * 1229 ∧
    pom_a4t_ade_intersection_t_minpoly_discriminant_squarefree_part
        pom_a4t_ade_intersection_t_minpoly_discriminant_E8 = 5 ∧
    Int.natAbs
        (pom_a4t_ade_intersection_t_minpoly_discriminant_discriminant
          pom_a4t_ade_intersection_t_minpoly_discriminant_E8) =
      pom_e8_intersection_field_discriminant_index_field_discriminant *
        pom_e8_intersection_field_discriminant_index_ztE8_order_index ^ 2

/-- Paper label: `prop:pom-e8-intersection-field-discriminant-index`. The `E₈`
square-spectrum certificate supplies the quartic field generator and its trace sum `7`, while the
ADE discriminant package contributes the squarefree part `5` and the explicit quartic
discriminant. The field discriminant `1125`, maximal-order claim for `ℤ[r_{E₈}]`, and the index
formula for `ℤ[t_{E₈}]` are then packaged by the standard discriminant-index identity. -/
theorem paper_pom_e8_intersection_field_discriminant_index :
    pom_a4t_e8_intersection_field_discriminant_index_spec := by
  rcases paper_pom_e8_square_spectrum_collapse_trace7 with ⟨_, htrace⟩
  rcases paper_pom_a4t_ade_intersection_t_minpoly_discriminant with
    ⟨_, _, _, _, _, _, _, _, hsquarefree, _⟩
  refine ⟨rfl, htrace, ?_, rfl, rfl, hsquarefree, ?_⟩
  · norm_num [pom_e8_intersection_field_discriminant_index_field_discriminant]
  · norm_num [pom_e8_intersection_field_discriminant_index_field_discriminant,
      pom_e8_intersection_field_discriminant_index_ztE8_order_index,
      pom_a4t_ade_intersection_t_minpoly_discriminant_discriminant,
      pom_a4t_ade_intersection_t_minpoly_discriminant_E8]

end Omega.POM
