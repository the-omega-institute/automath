import Mathlib

namespace Omega.GroupUnification

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the full-parameter information normal-form theorem in
    `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp`.
    thm:normal-form -/
theorem paper_zero_jitter_normal_form
    {X : Type}
    (tau : ℕ → X → ℝ)
    (h L : ℝ → ℝ)
    (T : ℕ → X → ℝ)
    (B : ℝ → Bool → Bool → ℝ)
    (phiInv p : ℝ) (n : ℕ) (x : X) (x0 xn : Bool)
    (hNormal :
      tau n x - (n : ℝ) * h p =
        -L p * (T n x - (n : ℝ) * (1 - p) / (2 - p)) + B p x0 xn)
    (hParry : L p = 0 ↔ p = phiInv) :
    (tau n x - (n : ℝ) * h p =
        -L p * (T n x - (n : ℝ) * (1 - p) / (2 - p)) + B p x0 xn) ∧
      (L p = 0 ↔ p = phiInv) := by
  exact ⟨hNormal, hParry⟩

end Omega.GroupUnification
