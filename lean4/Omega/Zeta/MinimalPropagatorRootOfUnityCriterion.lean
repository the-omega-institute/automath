import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

theorem paper_xi_minimal_propagator_root_of_unity_criterion (n : ℕ) (hn : 1 ≤ n)
    (lambdaPlus lambdaMinus : ℂ) (hminus : lambdaMinus ≠ 0) :
    lambdaPlus ^ n + lambdaMinus ^ n = 0 ↔ (lambdaPlus / lambdaMinus) ^ n = -1 := by
  have _hn : 1 ≤ n := hn
  constructor
  · intro htrace
    have hpow : lambdaMinus ^ n ≠ 0 := pow_ne_zero n hminus
    rw [div_pow]
    rw [eq_neg_iff_add_eq_zero]
    field_simp [hpow]
    simpa using htrace
  · intro hroot
    have hpow : lambdaMinus ^ n ≠ 0 := pow_ne_zero n hminus
    rw [div_pow] at hroot
    have hscaled : lambdaPlus ^ n / lambdaMinus ^ n * lambdaMinus ^ n =
        (-1 : ℂ) * lambdaMinus ^ n := by
      rw [hroot]
    rw [div_mul_cancel₀ _ hpow] at hscaled
    calc
      lambdaPlus ^ n + lambdaMinus ^ n = (-1 : ℂ) * lambdaMinus ^ n + lambdaMinus ^ n := by
        rw [hscaled]
      _ = 0 := by ring

end Omega.Zeta
