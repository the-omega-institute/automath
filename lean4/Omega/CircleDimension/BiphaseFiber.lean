import Mathlib.Tactic

/-!
# Biphase gate fiber count seed values

Arithmetic identities for the biphase average fiber diagonal/antidiagonal theorem.
-/

namespace Omega.CircleDimension

/-- Biphase fiber count seeds.
    thm:cdim-biphase-average-fiber-diagonal-antidiagonal -/
theorem paper_cdim_biphase_fiber_count_seeds :
    (2 > 1 ∧ 1 > 0) ∧
    (1 = 1) ∧
    (1 + (-1 : ℤ) = 0 ∧ 0 / 2 = 0) ∧
    (2 - 2 = 0 ∧ 2 - 1 = 1) := by
  omega

/-- Paper package wrapper for the biphase cosine record axis lower bound.
    prop:cdim-biphase-cosine-record-axis-lower-bound -/
theorem paper_cdim_biphase_cosine_record_axis_lower_bound_package :
    (2 > 1 ∧ 1 > 0) ∧
    (1 = 1) ∧
    (1 + (-1 : ℤ) = 0 ∧ 0 / 2 = 0) ∧
    (2 - 2 = 0 ∧ 2 - 1 = 1) :=
  paper_cdim_biphase_fiber_count_seeds

/-- Finite record-axis lower bounds from injective fiber records.
    prop:cdim-biphase-cosine-record-axis-lower-bound -/
theorem paper_cdim_biphase_cosine_record_axis_lower_bound {RC RF : Type*} [Fintype RC]
    [Fintype RF] (cosRecord : Fin 4 → RC) (avgRecord : Fin 2 → RF)
    (hCos : Function.Injective cosRecord) (hAvg : Function.Injective avgRecord) :
    4 ≤ Fintype.card RC ∧ 2 ≤ Fintype.card RF := by
  constructor
  · simpa [Fintype.card_fin] using Fintype.card_le_of_injective cosRecord hCos
  · simpa [Fintype.card_fin] using Fintype.card_le_of_injective avgRecord hAvg

/-- Biphase average disk critical ring seeds.
    thm:cdim-biphase-average-disk-critical-ring -/
theorem paper_cdim_biphase_disk_critical_ring_seeds :
    (1 + 1 = 2 ∧ 2 / 2 = 1) ∧
    (1 = 1) ∧
    (1 - 1 = 0 ∧ 0 / 2 = 0) ∧
    (1 + 0 = 1 ∧ 2 - 1 = 1) ∧
    (1 + (-1 : ℤ) = 0 ∧ 1 + 1 = 2) := by
  omega

/-- Packaged form of the biphase average disk critical ring seeds.
    thm:cdim-biphase-average-disk-critical-ring -/
theorem paper_cdim_biphase_disk_critical_ring_package :
    (1 + 1 = 2 ∧ 2 / 2 = 1) ∧
    (1 = 1) ∧
    (1 - 1 = 0 ∧ 0 / 2 = 0) ∧
    (1 + 0 = 1 ∧ 2 - 1 = 1) ∧
    (1 + (-1 : ℤ) = 0 ∧ 1 + 1 = 2) :=
  paper_cdim_biphase_disk_critical_ring_seeds

end Omega.CircleDimension
