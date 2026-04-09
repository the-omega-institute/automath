import Mathlib.Tactic
import Mathlib.Data.Nat.Digits.Defs

namespace Omega.SPG.ProuhetThueMorsePowerSum

open Finset

/-- Binary digit sum `s_2(n)`.
    thm:spg-prouhet-thue-morse-obstruction-dyadic-polyclube-flux-moments -/
def s₂ (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- Thue-Morse sign `τ(j) = (-1)^{s_2(j)}`.
    thm:spg-prouhet-thue-morse-obstruction-dyadic-polyclube-flux-moments -/
def tau (j : ℕ) : ℤ := (-1) ^ (s₂ j)

/-- Concrete values: `τ(0) = 1`.
    thm:spg-prouhet-thue-morse-obstruction-dyadic-polyclube-flux-moments -/
theorem tau_zero : tau 0 = 1 := by
  unfold tau s₂
  simp

/-- `τ(1) = -1`.
    thm:spg-prouhet-thue-morse-obstruction-dyadic-polyclube-flux-moments -/
theorem tau_one : tau 1 = -1 := by
  unfold tau s₂
  simp

/-- `τ(2) = -1` (since `s_2(2) = 1`).
    thm:spg-prouhet-thue-morse-obstruction-dyadic-polyclube-flux-moments -/
theorem tau_two : tau 2 = -1 := by
  unfold tau s₂
  decide

/-- `τ(3) = 1` (since `s_2(3) = 2`).
    thm:spg-prouhet-thue-morse-obstruction-dyadic-polyclube-flux-moments -/
theorem tau_three : tau 3 = 1 := by
  unfold tau s₂
  decide

/-- PTM power sum at `m = 1, ℓ = 0`: `τ(0) + τ(1) = 0`.
    thm:spg-prouhet-thue-morse-obstruction-dyadic-polyclube-flux-moments -/
theorem ptm_power_sum_m1_l0 :
    ∑ j ∈ Finset.range 2, tau j * (j : ℤ)^0 = 0 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [tau_zero, tau_one]
  ring

/-- PTM power sum at `m = 2, ℓ = 0`: `τ(0)+τ(1)+τ(2)+τ(3) = 0`.
    thm:spg-prouhet-thue-morse-obstruction-dyadic-polyclube-flux-moments -/
theorem ptm_power_sum_m2_l0 :
    ∑ j ∈ Finset.range 4, tau j * (j : ℤ)^0 = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, Finset.sum_range_succ,
      show (3 : ℕ) = 2 + 1 from rfl, Finset.sum_range_succ,
      show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ,
      Finset.sum_range_one]
  rw [tau_zero, tau_one, tau_two, tau_three]
  ring

/-- PTM power sum at `m = 2, ℓ = 1`: `0·τ(0)+1·τ(1)+2·τ(2)+3·τ(3) = 0+(-1)+(-2)+3 = 0`.
    thm:spg-prouhet-thue-morse-obstruction-dyadic-polyclube-flux-moments -/
theorem ptm_power_sum_m2_l1 :
    ∑ j ∈ Finset.range 4, tau j * (j : ℤ)^1 = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, Finset.sum_range_succ,
      show (3 : ℕ) = 2 + 1 from rfl, Finset.sum_range_succ,
      show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ,
      Finset.sum_range_one]
  rw [tau_zero, tau_one, tau_two, tau_three]
  ring

/-- Paper package (concrete `m ≤ 2` instances).
    thm:spg-prouhet-thue-morse-obstruction-dyadic-polyclube-flux-moments -/
theorem paper_spg_prouhet_thue_morse_power_sum_concrete :
    (∑ j ∈ Finset.range 2, tau j * (j : ℤ)^0 = 0) ∧
    (∑ j ∈ Finset.range 4, tau j * (j : ℤ)^0 = 0) ∧
    (∑ j ∈ Finset.range 4, tau j * (j : ℤ)^1 = 0) :=
  ⟨ptm_power_sum_m1_l0, ptm_power_sum_m2_l0, ptm_power_sum_m2_l1⟩

end Omega.SPG.ProuhetThueMorsePowerSum
