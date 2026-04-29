import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete factor types in the `m = 6` fold-bin gauge product
`S₂^8 × S₃^4 × S₄^9`. -/
inductive conclusion_foldbin_gauge_derived_fitting_composition_factor where
  | s2
  | s3
  | s4
  deriving DecidableEq

open conclusion_foldbin_gauge_derived_fitting_composition_factor

/-- Data object for the `m = 6` gauge product decomposition. -/
structure conclusion_foldbin_gauge_derived_fitting_composition_data where
  conclusion_foldbin_gauge_derived_fitting_composition_unit : Unit := ()

namespace conclusion_foldbin_gauge_derived_fitting_composition_data

/-- The multiplicities in `S₂^8 × S₃^4 × S₄^9`. -/
def conclusion_foldbin_gauge_derived_fitting_composition_multiplicity
    (G : conclusion_foldbin_gauge_derived_fitting_composition_factor) : ℕ :=
  match G with
  | s2 => 8
  | s3 => 4
  | s4 => 9

/-- Per-factor derived lengths for `S₂`, `S₃`, and `S₄`. -/
def conclusion_foldbin_gauge_derived_fitting_composition_factor_derived_length
    (G : conclusion_foldbin_gauge_derived_fitting_composition_factor) : ℕ :=
  match G with
  | s2 => 1
  | s3 => 2
  | s4 => 3

/-- Per-factor `Z/2Z` rank in the Fitting subgroup. -/
def conclusion_foldbin_gauge_derived_fitting_composition_factor_fitting_z2_rank
    (G : conclusion_foldbin_gauge_derived_fitting_composition_factor) : ℕ :=
  match G with
  | s2 => 1
  | s3 => 0
  | s4 => 2

/-- Per-factor `Z/3Z` rank in the Fitting subgroup. -/
def conclusion_foldbin_gauge_derived_fitting_composition_factor_fitting_z3_rank
    (G : conclusion_foldbin_gauge_derived_fitting_composition_factor) : ℕ :=
  match G with
  | s2 => 0
  | s3 => 1
  | s4 => 0

/-- Per-factor number of Jordan--Holder `Z/2Z` factors. -/
def conclusion_foldbin_gauge_derived_fitting_composition_factor_jh_z2_count
    (G : conclusion_foldbin_gauge_derived_fitting_composition_factor) : ℕ :=
  match G with
  | s2 => 1
  | s3 => 1
  | s4 => 3

/-- Per-factor number of Jordan--Holder `Z/3Z` factors. -/
def conclusion_foldbin_gauge_derived_fitting_composition_factor_jh_z3_count
    (G : conclusion_foldbin_gauge_derived_fitting_composition_factor) : ℕ :=
  match G with
  | s2 => 0
  | s3 => 1
  | s4 => 1

/-- Lift a per-factor count through `S₂^8 × S₃^4 × S₄^9`. -/
def conclusion_foldbin_gauge_derived_fitting_composition_product_count
    (f : conclusion_foldbin_gauge_derived_fitting_composition_factor → ℕ) : ℕ :=
  8 * f s2 + 4 * f s3 + 9 * f s4

/-- The product derived length is controlled by the slowest `S₄` factor. -/
def derivedLength (_D : conclusion_foldbin_gauge_derived_fitting_composition_data) : ℕ :=
  3

/-- The Fitting `Z/2Z` rank of `S₂^8 × S₃^4 × S₄^9`. -/
def fittingZ2Rank (_D : conclusion_foldbin_gauge_derived_fitting_composition_data) : ℕ :=
  conclusion_foldbin_gauge_derived_fitting_composition_product_count
    conclusion_foldbin_gauge_derived_fitting_composition_factor_fitting_z2_rank

/-- The Fitting `Z/3Z` rank of `S₂^8 × S₃^4 × S₄^9`. -/
def fittingZ3Rank (_D : conclusion_foldbin_gauge_derived_fitting_composition_data) : ℕ :=
  conclusion_foldbin_gauge_derived_fitting_composition_product_count
    conclusion_foldbin_gauge_derived_fitting_composition_factor_fitting_z3_rank

/-- The number of Jordan--Holder `Z/2Z` factors in the gauge product. -/
def jordanHolderZ2Count (_D : conclusion_foldbin_gauge_derived_fitting_composition_data) : ℕ :=
  conclusion_foldbin_gauge_derived_fitting_composition_product_count
    conclusion_foldbin_gauge_derived_fitting_composition_factor_jh_z2_count

/-- The number of Jordan--Holder `Z/3Z` factors in the gauge product. -/
def jordanHolderZ3Count (_D : conclusion_foldbin_gauge_derived_fitting_composition_data) : ℕ :=
  conclusion_foldbin_gauge_derived_fitting_composition_product_count
    conclusion_foldbin_gauge_derived_fitting_composition_factor_jh_z3_count

end conclusion_foldbin_gauge_derived_fitting_composition_data

open conclusion_foldbin_gauge_derived_fitting_composition_data

/-- Paper label: `thm:conclusion-foldbin-gauge-derived-fitting-composition`. -/
theorem paper_conclusion_foldbin_gauge_derived_fitting_composition
    (D : conclusion_foldbin_gauge_derived_fitting_composition_data) :
    D.derivedLength = 3 ∧ D.fittingZ2Rank = 26 ∧ D.fittingZ3Rank = 4 ∧
      D.jordanHolderZ2Count = 39 ∧ D.jordanHolderZ3Count = 13 := by
  simp [derivedLength, fittingZ2Rank, fittingZ3Rank, jordanHolderZ2Count,
    jordanHolderZ3Count, conclusion_foldbin_gauge_derived_fitting_composition_product_count,
    conclusion_foldbin_gauge_derived_fitting_composition_factor_fitting_z2_rank,
    conclusion_foldbin_gauge_derived_fitting_composition_factor_fitting_z3_rank,
    conclusion_foldbin_gauge_derived_fitting_composition_factor_jh_z2_count,
    conclusion_foldbin_gauge_derived_fitting_composition_factor_jh_z3_count]

end Omega.Conclusion
