import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9x-decoding-anomaly-nineteen-bit-gap`. -/
theorem paper_xi_time_part9x_decoding_anomaly_nineteen_bit_gap (b_anom b_inv : Nat)
    (hanom : b_anom = 21) (hinv : b_inv = 2) :
    b_anom - b_inv = 19 ∧ 2 ^ b_anom / 2 ^ b_inv = (2 : Nat) ^ 19 := by
  subst b_anom
  subst b_inv
  norm_num

end Omega.Zeta
