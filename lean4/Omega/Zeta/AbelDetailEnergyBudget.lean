import Mathlib.Tactic
import Omega.Zeta.AbelHardyEnergyDecimationOrthogonal

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `prop:abel-detail-energy-budget`. -/
theorem paper_abel_detail_energy_budget (a : ℕ → ℚ) (m N : ℕ) (hm : 0 < m) :
    let coarse := Finset.sum (Finset.range N) (fun q => (a (m * q)) ^ 2)
    let detail :=
      Finset.sum (Finset.range (m - 1))
        (fun j => Finset.sum (Finset.range N) (fun q => (a (m * q + (j + 1))) ^ 2))
    detail = Finset.sum (Finset.range (m * N)) (fun n => (a n) ^ 2) - coarse ∧
      0 ≤ detail ∧
      ((∃ j,
          j < m ∧ 0 < j ∧ 0 < Finset.sum (Finset.range N) (fun q => (a (m * q + j)) ^ 2)) →
        0 < detail) := by
  dsimp
  let channel : ℕ → ℚ := fun j => Finset.sum (Finset.range N) (fun q => (a (m * q + j)) ^ 2)
  let coarse : ℚ := channel 0
  let detail : ℚ := Finset.sum (Finset.range (m - 1)) (fun j => channel (j + 1))
  let total : ℚ := Finset.sum (Finset.range (m * N)) (fun n => (a n) ^ 2)
  have hsplit :
      total = Finset.sum (Finset.range m) channel := by
    simpa [total, channel] using (paper_abel_hardy_energy_decimation_orthogonal a m N hm).1
  have hsplit_detail :
      Finset.sum (Finset.range m) channel = detail + coarse := by
    simpa [channel, coarse, detail, Nat.sub_add_cancel hm] using
      (Finset.sum_range_succ'
        (fun j => Finset.sum (Finset.range N) (fun q => (a (m * q + j)) ^ 2)) (m - 1))
  have htotal :
      total = detail + coarse := by
    rw [hsplit, hsplit_detail]
  have hdetail_eq : detail = total - coarse := by
    linarith
  have hchannel_nonneg : ∀ j : ℕ, 0 ≤ channel j := by
    intro j
    dsimp [channel]
    exact Finset.sum_nonneg (fun q _ => sq_nonneg (a (m * q + j)))
  have hdetail_nonneg : 0 ≤ detail := by
    dsimp [detail]
    exact Finset.sum_nonneg (fun j _ => hchannel_nonneg (j + 1))
  refine ⟨hdetail_eq, hdetail_nonneg, ?_⟩
  intro hpos
  rcases hpos with ⟨j, hjm, hj0, hjpos⟩
  rcases Nat.exists_eq_succ_of_ne_zero hj0.ne' with ⟨k, rfl⟩
  have hk : k < m - 1 := by
    omega
  have hterm_le : channel (k + 1) ≤ detail := by
    dsimp [detail]
    exact Finset.single_le_sum (fun i _ => hchannel_nonneg (i + 1)) (Finset.mem_range.mpr hk)
  linarith

end Omega.Zeta
