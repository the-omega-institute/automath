import Mathlib
import Omega.Folding.FoldGaugeAnomalyP10LeyangHTripleProduct

namespace Omega.Folding

/-- Density of one conjugacy class inside a finite Galois factor of the audited triple product. -/
def fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_class_density
    (classSize groupOrder : ℕ) : ℚ :=
  (classSize : ℚ) / groupOrder

/-- Product Chebotarev density for the `S₁₀ × S₃ × S₁₉` factorization. -/
def fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_density
    (C10 C3 C19 : ℕ) : ℚ :=
  fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_class_density
      C10 (Nat.factorial 10) *
    fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_class_density
      C3 (Nat.factorial 3) *
    fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_class_density
      C19 (Nat.factorial 19)

/-- Paper label: `cor:fold-gauge-anomaly-P10-leyang-H-chebotarev-triple-product`. -/
theorem paper_fold_gauge_anomaly_P10_leyang_H_chebotarev_triple_product
    (C10 C3 C19 : ℕ) :
    fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_density C10 C3 C19 =
      (C10 : ℚ) / Nat.factorial 10 * ((C3 : ℚ) / Nat.factorial 3) *
        ((C19 : ℚ) / Nat.factorial 19) := by
  rcases paper_fold_gauge_anomaly_P10_leyang_H_triple_product with ⟨_, _⟩
  simp [fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_density,
    fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_class_density, mul_assoc]

end Omega.Folding
