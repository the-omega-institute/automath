import Mathlib.Tactic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the explicit coefficient package in the
    eighth-order Poisson KL expansion.
    thm:poisson-kl-eighth -/
theorem paper_circle_dimension_poisson_kl_eighth
    (C4 C6 C8a C8b sigma mu3 mu4 mu5 mu6 : ℝ)
    (hC4 : 8 * C4 = sigma ^ 4)
    (hC6 : 64 * C6 = sigma ^ 6 + 6 * mu3 ^ 2 - 8 * sigma ^ 2 * mu4)
    (hC8a : 256 * C8a = 3 * sigma ^ 8 - 12 * sigma ^ 4 * mu4 + 9 * sigma ^ 2 * mu3 ^ 2)
    (hC8b : 256 * C8b = 12 * sigma ^ 2 * mu6 - 30 * mu3 * mu5 + 20 * mu4 ^ 2) :
    C4 = sigma ^ 4 / 8 ∧
      C6 = (sigma ^ 6 + 6 * mu3 ^ 2 - 8 * sigma ^ 2 * mu4) / 64 ∧
      C8a = (3 * sigma ^ 8 - 12 * sigma ^ 4 * mu4 + 9 * sigma ^ 2 * mu3 ^ 2) / 256 ∧
      C8b = (12 * sigma ^ 2 * mu6 - 30 * mu3 * mu5 + 20 * mu4 ^ 2) / 256 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- Paper label: `thm:poisson-kl-eighth`. Wrapper exposing the exact paper-facing theorem name for
the already formalized eighth-order Poisson KL coefficient package. -/
theorem paper_poisson_kl_eighth
    (C4 C6 C8a C8b sigma mu3 mu4 mu5 mu6 : ℝ)
    (hC4 : 8 * C4 = sigma ^ 4)
    (hC6 : 64 * C6 = sigma ^ 6 + 6 * mu3 ^ 2 - 8 * sigma ^ 2 * mu4)
    (hC8a : 256 * C8a = 3 * sigma ^ 8 - 12 * sigma ^ 4 * mu4 + 9 * sigma ^ 2 * mu3 ^ 2)
    (hC8b : 256 * C8b = 12 * sigma ^ 2 * mu6 - 30 * mu3 * mu5 + 20 * mu4 ^ 2) :
    C4 = sigma ^ 4 / 8 ∧
      C6 = (sigma ^ 6 + 6 * mu3 ^ 2 - 8 * sigma ^ 2 * mu4) / 64 ∧
      C8a = (3 * sigma ^ 8 - 12 * sigma ^ 4 * mu4 + 9 * sigma ^ 2 * mu3 ^ 2) / 256 ∧
      C8b = (12 * sigma ^ 2 * mu6 - 30 * mu3 * mu5 + 20 * mu4 ^ 2) / 256 := by
  simpa using paper_circle_dimension_poisson_kl_eighth C4 C6 C8a C8b sigma mu3 mu4 mu5 mu6 hC4 hC6
    hC8a hC8b

end Omega.CircleDimension
