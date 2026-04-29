import Mathlib.Data.Fintype.Perm
import Omega.Folding.FoldGaugeAnomalyP10LeyangHChebotarevTripleProduct
import Omega.Folding.KilloLeyangTwoBranchFieldsProductGalois

namespace Omega.Folding

/-- The audited `10`-cycle class in `S₁₀` has cardinality `(10 - 1)!`. -/
def fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_p10_ten_cycle_class_size : ℕ :=
  Nat.factorial 9

/-- The transposition class in `S₃` has cardinality `3`. -/
def fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_leyang_transposition_class_size :
    ℕ :=
  3

/-- The identity class in `S₃` has cardinality `1`. -/
def fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_leyang_identity_class_size : ℕ :=
  1

/-- Density of the irreducible Lee--Yang root event: `10`-cycle on the `P10` side and a
transposition on the Lee--Yang cubic side. -/
def fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_irreducible_density : ℚ :=
  fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_class_density
      fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_p10_ten_cycle_class_size
      (Nat.factorial 10) *
    fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_class_density
      fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_leyang_transposition_class_size
      killoLeyangCubicBranchFieldOrder

/-- Density of the split Lee--Yang root event: `10`-cycle on the `P10` side and the identity class
on the Lee--Yang cubic side. -/
def fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_split_density : ℚ :=
  fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_class_density
      fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_p10_ten_cycle_class_size
      (Nat.factorial 10) *
    fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_class_density
      fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_leyang_identity_class_size
      killoLeyangCubicBranchFieldOrder

/-- Proposition-level wrapper for the audited irreducible/split density calculation. -/
def fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_statement : Prop :=
  fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_irreducible_density =
      ((1 : ℚ) / 10) * ((1 : ℚ) / 2) ∧
    fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_split_density =
      ((1 : ℚ) / 10) * ((1 : ℚ) / Nat.factorial 3) ∧
    fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_irreducible_density =
      (1 : ℚ) / 20 ∧
    fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_split_density =
      (1 : ℚ) / 60

/-- Paper label: `cor:fold-gauge-anomaly-P10-leyang-irreducible-root-split-densities`. -/
theorem paper_fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities :
    fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_statement := by
  have hp10 :
      fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_class_density
          fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_p10_ten_cycle_class_size
          (Nat.factorial 10) =
        (1 : ℚ) / 10 := by
    unfold fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_class_density
      fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_p10_ten_cycle_class_size
    norm_num [Nat.factorial]
  have htrans :
      fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_class_density
          fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_leyang_transposition_class_size
          killoLeyangCubicBranchFieldOrder =
        (1 : ℚ) / 2 := by
    unfold fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_class_density
      fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_leyang_transposition_class_size
      killoLeyangCubicBranchFieldOrder
    norm_num [Nat.factorial]
  have hid :
      fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_class_density
          fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_leyang_identity_class_size
          killoLeyangCubicBranchFieldOrder =
        (1 : ℚ) / Nat.factorial 3 := by
    unfold fold_gauge_anomaly_p10_leyang_h_chebotarev_triple_product_class_density
      fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_leyang_identity_class_size
      killoLeyangCubicBranchFieldOrder
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_irreducible_density
    rw [hp10, htrans]
  · unfold fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_split_density
    rw [hp10, hid]
  · calc
      fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_irreducible_density =
          ((1 : ℚ) / 10) * ((1 : ℚ) / 2) := by
            unfold fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_irreducible_density
            rw [hp10, htrans]
      _ = (1 : ℚ) / 20 := by norm_num
  · calc
      fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_split_density =
          ((1 : ℚ) / 10) * ((1 : ℚ) / Nat.factorial 3) := by
            unfold fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_split_density
            rw [hp10, hid]
      _ = (1 : ℚ) / 60 := by norm_num [Nat.factorial]

end Omega.Folding
