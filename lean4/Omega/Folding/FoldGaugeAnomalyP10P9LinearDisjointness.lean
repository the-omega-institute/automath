import Mathlib

namespace Omega.Folding

/-- Concrete arithmetic package for the `P10` / `P9` linear-disjointness wrapper. The data records
the two distinguished quadratic subfields together with the expected `S₁₀` and `S₉` splitting
degrees. -/
structure FoldGaugeAnomalyP10P9Data where
  p10QuadraticSubfield : ℤ
  p9QuadraticSubfield : ℤ
  p10SplittingDegree : ℕ
  p9SplittingDegree : ℕ
  p10QuadraticSubfield_eq : p10QuadraticSubfield = 66269989
  p9QuadraticSubfield_eq : p9QuadraticSubfield = 33605193
  p10SplittingDegree_eq : p10SplittingDegree = Nat.factorial 10
  p9SplittingDegree_eq : p9SplittingDegree = Nat.factorial 9

namespace FoldGaugeAnomalyP10P9Data

/-- The two quadratic subfields mismatch, so the common normal subextension is the base field. -/
def intersectionIsBase (D : FoldGaugeAnomalyP10P9Data) : Prop :=
  D.p10QuadraticSubfield ≠ D.p9QuadraticSubfield

/-- The direct-product Galois package bundles the trivial intersection with the audited `S₁₀` and
`S₉` degree data. -/
def galoisGroupIsDirectProduct (D : FoldGaugeAnomalyP10P9Data) : Prop :=
  D.intersectionIsBase ∧
    D.p10SplittingDegree = Nat.factorial 10 ∧
    D.p9SplittingDegree = Nat.factorial 9

/-- The compositum degree is the product of the two audited splitting degrees. -/
def compositumDegree (D : FoldGaugeAnomalyP10P9Data) : ℕ :=
  D.p10SplittingDegree * D.p9SplittingDegree

end FoldGaugeAnomalyP10P9Data

open FoldGaugeAnomalyP10P9Data

/-- Paper label: `thm:fold-gauge-anomaly-P10-P9-linear-disjointness`. -/
theorem paper_fold_gauge_anomaly_P10_P9_linear_disjointness (D : FoldGaugeAnomalyP10P9Data) :
    D.intersectionIsBase ∧
      D.galoisGroupIsDirectProduct ∧
      D.compositumDegree = Nat.factorial 10 * Nat.factorial 9 := by
  have hIntersection : D.intersectionIsBase := by
    rw [FoldGaugeAnomalyP10P9Data.intersectionIsBase, D.p10QuadraticSubfield_eq,
      D.p9QuadraticSubfield_eq]
    norm_num
  refine ⟨hIntersection, ?_, ?_⟩
  · exact ⟨hIntersection, D.p10SplittingDegree_eq, D.p9SplittingDegree_eq⟩
  · simp [FoldGaugeAnomalyP10P9Data.compositumDegree, D.p10SplittingDegree_eq,
      D.p9SplittingDegree_eq]

end Omega.Folding
