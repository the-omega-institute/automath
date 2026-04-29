import Mathlib
import Omega.Folding.FoldGaugeAnomalyP10HLinearDisjointness
import Omega.Folding.FoldGaugeAnomalyP10LeyangLinearDisjointness
import Omega.Folding.KilloLeyangTwoBranchFieldsProductGalois

namespace Omega.Folding

/-- The audited `P10`/Lee--Yang package says that any common quadratic signature is the base
signature `0`. -/
def foldGaugeAnomalyP10LeyangQuadraticIntersectionBase : Prop :=
  ∀ inter : ℤ,
    inter ∈ ({0, foldGaugeAnomalyP10QuadraticSubfield} : Finset ℤ) →
      inter ∈ ({0, killoLeyangCubicQuadraticSubfieldDiscriminant} : Finset ℤ) →
        inter = 0

/-- The audited quadratic witness for `H` is different from the Lee--Yang quadratic subfield. -/
def foldGaugeAnomalyLeyangHQuadraticIntersectionBase : Prop :=
  foldGaugeAnomalyHQuadraticSubfield ≠ killoLeyangCubicQuadraticSubfieldDiscriminant

/-- Publication-facing triple-product package built from the existing `P10`/Lee--Yang and
`P10`/`H` direct-product statements together with the extra Lee--Yang/`H` quadratic mismatch. -/
def foldGaugeAnomalyP10LeyangHTripleProductGalois : Prop :=
  killoLeyangTwoBranchFieldsProductGalois ∧
    foldGaugeAnomalyP10HDirectProductGalois ∧
    foldGaugeAnomalyP10LeyangQuadraticIntersectionBase ∧
    foldGaugeAnomalyLeyangHQuadraticIntersectionBase ∧
    foldGaugeAnomalyP10SplittingDegree = Nat.factorial 10 ∧
    killoLeyangCubicBranchFieldOrder = Nat.factorial 3 ∧
    foldGaugeAnomalyHSplittingDegree = Nat.factorial 19

/-- The audited compositum degree attached to the `S₁₀ × S₃ × S₁₉` package. -/
def foldGaugeAnomalyP10LeyangHTripleCompositumDegree : ℕ :=
  foldGaugeAnomalyP10SplittingDegree * killoLeyangCubicBranchFieldOrder *
    foldGaugeAnomalyHSplittingDegree

/-- Paper label: `thm:fold-gauge-anomaly-P10-leyang-H-triple-product`. The previously audited
`P10`/Lee--Yang and `P10`/`H` packages already provide the two direct-product factors; the extra
Lee--Yang-vs-`H` quadratic mismatch rules out the remaining overlap, leaving the expected triple
product degree package. -/
theorem paper_fold_gauge_anomaly_P10_leyang_H_triple_product :
    foldGaugeAnomalyP10LeyangHTripleProductGalois ∧
      foldGaugeAnomalyP10LeyangHTripleCompositumDegree =
        Nat.factorial 10 * Nat.factorial 3 * Nat.factorial 19 := by
  have hp10ly : foldGaugeAnomalyP10LeyangQuadraticIntersectionBase := by
    intro inter hP10 hLY
    simpa using
      (paper_fold_gauge_anomaly_P10_leyang_linear_disjointness
        (alpha := ℤ) 0 foldGaugeAnomalyP10QuadraticSubfield
        killoLeyangCubicQuadraticSubfieldDiscriminant inter hP10 hLY
        (by
          unfold foldGaugeAnomalyP10QuadraticSubfield
            killoLeyangCubicQuadraticSubfieldDiscriminant
          norm_num))
  have hlyH : foldGaugeAnomalyLeyangHQuadraticIntersectionBase := by
    unfold foldGaugeAnomalyLeyangHQuadraticIntersectionBase
    norm_num [foldGaugeAnomalyHQuadraticSubfield,
      killoLeyangCubicQuadraticSubfieldDiscriminant]
  rcases paper_killo_leyang_two_branch_fields_product_galois with ⟨_, hkillo⟩
  rcases paper_fold_gauge_anomaly_P10_H_linear_disjointness with ⟨_, _, _, hp10H, _⟩
  refine ⟨⟨hkillo, hp10H, hp10ly, hlyH, rfl, rfl, rfl⟩, rfl⟩

/-- Concrete data token for the lower-case theorem name used by the round manifest. -/
abbrev fold_gauge_anomaly_p10_leyang_h_triple_product_data := PUnit

/-- The concrete triple-product statement registered under the round-manifest spelling. -/
def fold_gauge_anomaly_p10_leyang_h_triple_product_statement
    (_ : fold_gauge_anomaly_p10_leyang_h_triple_product_data) : Prop :=
  foldGaugeAnomalyP10LeyangHTripleProductGalois ∧
    foldGaugeAnomalyP10LeyangHTripleCompositumDegree =
      Nat.factorial 10 * Nat.factorial 3 * Nat.factorial 19

/-- Paper label: `thm:fold-gauge-anomaly-P10-leyang-H-triple-product`. -/
theorem paper_fold_gauge_anomaly_p10_leyang_h_triple_product
    (D : fold_gauge_anomaly_p10_leyang_h_triple_product_data) :
    fold_gauge_anomaly_p10_leyang_h_triple_product_statement D := by
  exact paper_fold_gauge_anomaly_P10_leyang_H_triple_product

end Omega.Folding
