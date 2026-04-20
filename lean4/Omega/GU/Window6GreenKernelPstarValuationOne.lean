import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- If `p⋆` divides the common denominator but `p⋆²` does not, then the `p⋆`-adic exponent of the
denominator is exactly `1`. -/
theorem paper_window6_green_kernel_pstar_valuation_one (D pstar : Nat) (hp : Nat.Prime pstar)
    (hdiv : pstar ∣ D) (hnot_sq : ¬ pstar ^ 2 ∣ D) : D.factorization pstar = 1 := by
  have hD_ne : D ≠ 0 := by
    intro hD
    apply hnot_sq
    simp [hD]
  have hpow_one : pstar ^ 1 ∣ D := by
    simpa using hdiv
  have hge_one : 1 ≤ D.factorization pstar := by
    simpa using (Nat.Prime.pow_dvd_iff_le_factorization hp hD_ne).mp hpow_one
  have hlt_two : D.factorization pstar < 2 := by
    have hnot_ge_two : ¬ 2 ≤ D.factorization pstar := by
      intro htwo
      apply hnot_sq
      exact (Nat.Prime.pow_dvd_iff_le_factorization hp hD_ne).mpr htwo
    omega
  omega

end Omega.GU
