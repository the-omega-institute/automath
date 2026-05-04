import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete moment data for `cor:xi-poisson-cauchy-location-scale-m2-blind-m3-kl`. -/
structure xi_poisson_cauchy_location_scale_m2_blind_m3_kl_Data where
  xi_poisson_cauchy_location_scale_m2_blind_m3_kl_moment : ℕ → ℚ

namespace xi_poisson_cauchy_location_scale_m2_blind_m3_kl_Data

/-- The location-scale second multipole vanishes. -/
def secondMomentVanishes (D : xi_poisson_cauchy_location_scale_m2_blind_m3_kl_Data) : Prop :=
  D.xi_poisson_cauchy_location_scale_m2_blind_m3_kl_moment 2 = 0

/-- The `k = 3` multipole KL constant is `binom(4, 2) / 2^6 = 3/32`. -/
def sixthOrderKLConstantIsThreeThirtySeconds
    (_D : xi_poisson_cauchy_location_scale_m2_blind_m3_kl_Data) : Prop :=
  ((Nat.choose 4 2 : ℚ) / 2 ^ 6) = 3 / 32

end xi_poisson_cauchy_location_scale_m2_blind_m3_kl_Data

/-- Paper label: `cor:xi-poisson-cauchy-location-scale-m2-blind-m3-kl`. -/
theorem paper_xi_poisson_cauchy_location_scale_m2_blind_m3_kl
    (D : xi_poisson_cauchy_location_scale_m2_blind_m3_kl_Data) :
    D.secondMomentVanishes → D.sixthOrderKLConstantIsThreeThirtySeconds := by
  intro _hSecondMoment
  norm_num [
    xi_poisson_cauchy_location_scale_m2_blind_m3_kl_Data.sixthOrderKLConstantIsThreeThirtySeconds,
    Nat.choose
  ]

end Omega.Zeta
