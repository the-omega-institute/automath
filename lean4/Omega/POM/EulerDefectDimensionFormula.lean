import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Omega.POM.CrossAnomMobiusAnovaDimensionTheory
import Omega.POM.EulerDefectQuotientCoordinate

namespace Omega.POM

open Finset
open scoped BigOperators

/-- The Euler-defect dimension formula uses the same finite-axis size data as the ambient
Möbius--ANOVA count. -/
abbrev pom_euler_defect_dimension_formula_data :=
  pom_cross_anom_mobius_anova_dimension_theory_data

/-- The quotient dimension is the sum of all pure components of order at least two. -/
def pom_euler_defect_dimension_formula_quotient_dimension
    (D : pom_euler_defect_dimension_formula_data) : ℕ :=
  Finset.sum
    ((((Finset.univ : Finset (Fin D.k)).powerset.erase ∅).filter (fun S => 2 ≤ S.card)))
    (fun S => pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S)

/-- Publication-facing package: the quotient-coordinate theorem is available, and in the finite
axis model its dimension is both the normalized-minus-axis count and the subset expansion over
all components of order at least two. -/
def pom_euler_defect_dimension_formula_statement
    (D : pom_euler_defect_dimension_formula_data) : Prop :=
  (pom_euler_defect_dimension_formula_quotient_dimension D =
    pom_cross_anom_mobius_anova_dimension_theory_normalized_dimension D -
      pom_cross_anom_mobius_anova_dimension_theory_axis_dimension D) ∧
  (pom_euler_defect_dimension_formula_quotient_dimension D =
    Finset.sum
      ((((Finset.univ : Finset (Fin D.k)).powerset.erase ∅).filter (fun S => 2 ≤ S.card)))
      (fun S => pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S))

lemma pom_euler_defect_dimension_formula_filter_not_singleton_eq_filter_ge_two
    (D : pom_euler_defect_dimension_formula_data) :
    ((((Finset.univ : Finset (Fin D.k)).powerset.erase ∅).filter (fun S => S.card ≠ 1))) =
      ((((Finset.univ : Finset (Fin D.k)).powerset.erase ∅).filter (fun S => 2 ≤ S.card))) := by
  ext S
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hmem, hnot1⟩
    rcases Finset.mem_erase.mp hmem with ⟨hne, hsub⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨hne, hsub⟩, ?_⟩
    have hpos : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
    omega
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hmem, hge2⟩
    rcases Finset.mem_erase.mp hmem with ⟨hne, hsub⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨hne, hsub⟩, ?_⟩
    omega

/-- Paper label: `cor:pom-euler-defect-dimension-formula`. -/
theorem paper_pom_euler_defect_dimension_formula
    (D : pom_euler_defect_dimension_formula_data) :
    pom_euler_defect_dimension_formula_statement D := by
  let s : Finset (Finset (Fin D.k)) := ((Finset.univ : Finset (Fin D.k)).powerset.erase ∅)
  have hsplit :
      pom_cross_anom_mobius_anova_dimension_theory_axis_dimension D +
          Finset.sum
            (s.filter (fun S => S.card ≠ 1))
            (fun S => pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S) =
        Finset.sum s (fun S => pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S) := by
    simpa [pom_cross_anom_mobius_anova_dimension_theory_axis_dimension, s] using
      (Finset.sum_filter_add_sum_filter_not
        (s := s)
        (p := fun S => S.card = 1)
        (f := pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D))
  have hmain :
      pom_cross_anom_mobius_anova_dimension_theory_axis_dimension D +
          pom_euler_defect_dimension_formula_quotient_dimension D =
        pom_cross_anom_mobius_anova_dimension_theory_normalized_dimension D := by
    calc
      pom_cross_anom_mobius_anova_dimension_theory_axis_dimension D +
          pom_euler_defect_dimension_formula_quotient_dimension D =
        pom_cross_anom_mobius_anova_dimension_theory_axis_dimension D +
          Finset.sum
            (s.filter (fun S => S.card ≠ 1))
            (fun S => pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S) := by
              rw [pom_euler_defect_dimension_formula_filter_not_singleton_eq_filter_ge_two D]
              rfl
      _ = Finset.sum s (fun S => pom_cross_anom_mobius_anova_dimension_theory_pure_dimension D S) :=
        hsplit
      _ = pom_cross_anom_mobius_anova_dimension_theory_normalized_dimension D :=
        pom_cross_anom_mobius_anova_dimension_theory_nonempty_sum D
  let _ := paper_pom_euler_defect_quotient_coordinate
  refine ⟨?_, rfl⟩
  have hmain' :
      pom_euler_defect_dimension_formula_quotient_dimension D +
          pom_cross_anom_mobius_anova_dimension_theory_axis_dimension D =
        pom_cross_anom_mobius_anova_dimension_theory_normalized_dimension D := by
    simpa [add_comm] using hmain
  exact Nat.eq_sub_of_add_eq hmain'

end Omega.POM
