import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part60aaa-one-nat-unnormalized-ledger-rebate`. -/
theorem paper_xi_time_part60aaa_one_nat_unnormalized_ledger_rebate
    (A L kappa g err : ℕ → ℝ)
    (hA : ∀ m, kappa m = A m / (2 : ℝ) ^ m)
    (hL : ∀ m, g m = L m / (2 : ℝ) ^ m)
    (hDiff : ∀ m, kappa m - g m = 1 + err m) :
    (∀ m, L m / (2 : ℝ) ^ m = kappa m - 1 - err m) ∧
      (∀ m, L m = A m - (2 : ℝ) ^ m - err m * (2 : ℝ) ^ m) := by
  constructor
  · intro m
    rw [← hL m]
    linarith [hDiff m]
  · intro m
    have htwo : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
    have hnorm : L m / (2 : ℝ) ^ m = A m / (2 : ℝ) ^ m - 1 - err m := by
      rw [← hL m, ← hA m]
      linarith [hDiff m]
    field_simp [htwo] at hnorm
    linarith

end Omega.Zeta
