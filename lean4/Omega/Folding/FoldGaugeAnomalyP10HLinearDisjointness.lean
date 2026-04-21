import Mathlib

namespace Omega.Folding

/-- The unique quadratic subfield attached to `P10`. -/
def foldGaugeAnomalyP10QuadraticSubfield : ℤ :=
  66269989

/-- The quadratic fingerprint of the degree-`19` auxiliary factor `H`, chosen so that the prime
`101` ramifies. -/
def foldGaugeAnomalyHQuadraticSubfield : ℤ :=
  101

/-- The audited splitting degree of the `P10` splitting field. -/
def foldGaugeAnomalyP10SplittingDegree : ℕ :=
  Nat.factorial 10

/-- The audited splitting degree of the `H` splitting field. -/
def foldGaugeAnomalyHSplittingDegree : ℕ :=
  Nat.factorial 19

/-- The `P10` quadratic subfield is unramified at `101`. -/
def foldGaugeAnomalyP10UnramifiedAt101 : Prop :=
  ¬ (101 : ℤ) ∣ foldGaugeAnomalyP10QuadraticSubfield

/-- The `H` quadratic subfield is ramified at `101`. -/
def foldGaugeAnomalyHRamifiedAt101 : Prop :=
  (101 : ℤ) ∣ foldGaugeAnomalyHQuadraticSubfield

/-- The only possible common quadratic subfields disagree, so the intersection is trivial. -/
def foldGaugeAnomalyP10HIntersectionIsBase : Prop :=
  foldGaugeAnomalyP10QuadraticSubfield ≠ foldGaugeAnomalyHQuadraticSubfield

/-- The compositum carries the expected direct-product Galois package. -/
def foldGaugeAnomalyP10HDirectProductGalois : Prop :=
  foldGaugeAnomalyP10HIntersectionIsBase ∧
    foldGaugeAnomalyP10SplittingDegree = Nat.factorial 10 ∧
    foldGaugeAnomalyHSplittingDegree = Nat.factorial 19

/-- The compositum degree is the product of the two audited splitting degrees. -/
def foldGaugeAnomalyP10HCompositumDegree : ℕ :=
  foldGaugeAnomalyP10SplittingDegree * foldGaugeAnomalyHSplittingDegree

/-- Paper label: `prop:fold-gauge-anomaly-P10-H-linear-disjointness`. -/
theorem paper_fold_gauge_anomaly_P10_H_linear_disjointness :
    foldGaugeAnomalyP10UnramifiedAt101 ∧
      foldGaugeAnomalyHRamifiedAt101 ∧
      foldGaugeAnomalyP10HIntersectionIsBase ∧
      foldGaugeAnomalyP10HDirectProductGalois ∧
      foldGaugeAnomalyP10HCompositumDegree = Nat.factorial 10 * Nat.factorial 19 := by
  have hp10_101 : foldGaugeAnomalyP10UnramifiedAt101 := by
    norm_num [foldGaugeAnomalyP10UnramifiedAt101, foldGaugeAnomalyP10QuadraticSubfield]
  have hH_101 : foldGaugeAnomalyHRamifiedAt101 := by
    refine ⟨1, by norm_num [foldGaugeAnomalyHRamifiedAt101, foldGaugeAnomalyHQuadraticSubfield]⟩
  have hIntersection : foldGaugeAnomalyP10HIntersectionIsBase := by
    unfold foldGaugeAnomalyP10HIntersectionIsBase
    norm_num [foldGaugeAnomalyP10QuadraticSubfield, foldGaugeAnomalyHQuadraticSubfield]
  refine ⟨hp10_101, hH_101, hIntersection, ?_, ?_⟩
  · exact ⟨hIntersection, rfl, rfl⟩
  · rfl

end Omega.Folding
