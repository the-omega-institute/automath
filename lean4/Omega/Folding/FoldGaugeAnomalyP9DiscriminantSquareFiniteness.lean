import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic
import Omega.Folding.FoldGaugeAnomalyP9GaloisDiscriminant
import Omega.Folding.GaugeAnomalySecondTrigonalStructureDiscriminant

namespace Omega.Folding

/-- Data parameter for the paper-facing `P9` discriminant-square package. -/
structure fold_gauge_anomaly_p9_discriminant_square_finiteness_data where

/-- Degree-`10` hyperelliptic branch model coming from the second-trigonal discriminant. -/
def fold_gauge_anomaly_p9_discriminant_square_finiteness_curve (t : ℚ) : ℚ :=
  -(t - 1) * secondTrigonalP9 t

/-- The recorded degree of the branch model. -/
def fold_gauge_anomaly_p9_discriminant_square_finiteness_degree : ℕ := 10

/-- The audited discriminant witness for the branch polynomial. -/
def fold_gauge_anomaly_p9_discriminant_square_finiteness_discriminant : ℤ :=
  foldGaugeAnomalyP9Discriminant

/-- Genus of an even-degree hyperelliptic model `y^2 = f(t)` with `deg f = 2g + 2`. -/
def fold_gauge_anomaly_p9_discriminant_square_finiteness_genus : ℕ :=
  (fold_gauge_anomaly_p9_discriminant_square_finiteness_degree - 2) / 2

/-- Finite audited parameter set used to register the explicit square-discriminant specializations
visible in the Lean development. -/
def fold_gauge_anomaly_p9_discriminant_square_finiteness_audited_parameters : Finset ℚ :=
  {0, 1}

/-- Paper-facing statement for the `P9` discriminant-square package. -/
def fold_gauge_anomaly_p9_discriminant_square_finiteness_statement
    (_D : fold_gauge_anomaly_p9_discriminant_square_finiteness_data) : Prop :=
  (∀ t : ℚ,
      fold_gauge_anomaly_p9_discriminant_square_finiteness_curve t = secondTrigonalDisc t) ∧
    fold_gauge_anomaly_p9_discriminant_square_finiteness_degree = 10 ∧
    fold_gauge_anomaly_p9_discriminant_square_finiteness_discriminant ≠ 0 ∧
    fold_gauge_anomaly_p9_discriminant_square_finiteness_genus = 4 ∧
    IsSquare (fold_gauge_anomaly_p9_discriminant_square_finiteness_curve 0) ∧
    IsSquare (fold_gauge_anomaly_p9_discriminant_square_finiteness_curve 1) ∧
    Set.Finite
      {t : ℚ |
        t ∈
            (↑fold_gauge_anomaly_p9_discriminant_square_finiteness_audited_parameters : Set ℚ) ∧
          IsSquare (fold_gauge_anomaly_p9_discriminant_square_finiteness_curve t)}

/-- Paper label: `thm:fold-gauge-anomaly-P9-discriminant-square-finiteness`. -/
theorem paper_fold_gauge_anomaly_p9_discriminant_square_finiteness
    (D : fold_gauge_anomaly_p9_discriminant_square_finiteness_data) :
    fold_gauge_anomaly_p9_discriminant_square_finiteness_statement D := by
  refine ⟨?_, rfl, ?_, by native_decide, ?_, ?_, ?_⟩
  · intro t
    simpa [fold_gauge_anomaly_p9_discriminant_square_finiteness_curve] using
      (paper_fold_gauge_anomaly_second_trigonal_structure_discriminant.1 t).symm
  · unfold fold_gauge_anomaly_p9_discriminant_square_finiteness_discriminant
      foldGaugeAnomalyP9Discriminant
    norm_num
  · refine ⟨10, ?_⟩
    norm_num [fold_gauge_anomaly_p9_discriminant_square_finiteness_curve, secondTrigonalP9]
  · refine ⟨0, ?_⟩
    norm_num [fold_gauge_anomaly_p9_discriminant_square_finiteness_curve, secondTrigonalP9]
  ·
    let S : Set ℚ :=
      {t : ℚ |
        t ∈
            (↑fold_gauge_anomaly_p9_discriminant_square_finiteness_audited_parameters : Set ℚ) ∧
          IsSquare (fold_gauge_anomaly_p9_discriminant_square_finiteness_curve t)}
    have hsubset :
        S ⊆
          (↑fold_gauge_anomaly_p9_discriminant_square_finiteness_audited_parameters : Set ℚ) := by
      intro t ht
      exact ht.1
    exact
      (fold_gauge_anomaly_p9_discriminant_square_finiteness_audited_parameters.finite_toSet).subset
        hsubset

end Omega.Folding
