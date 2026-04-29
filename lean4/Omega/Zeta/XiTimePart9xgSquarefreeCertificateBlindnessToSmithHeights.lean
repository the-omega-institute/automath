import Mathlib.Tactic
import Omega.Zeta.KilloKernelSizeGeneralModulus

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9xg-squarefree-certificate-blindness-to-smith-heights`. -/
theorem paper_xi_time_part9xg_squarefree_certificate_blindness_to_smith_heights
    (p : ℕ) (hp : 2 ≤ p) :
    killoKernelSizeGeneralModulus 1 1 (p ^ 2) [p] = p ∧
      killoKernelSizeGeneralModulus 1 1 (p ^ 2) [p ^ 2] = p ^ 2 ∧
        killoKernelSizeGeneralModulus 1 1 (p ^ 2) [p] ≠
          killoKernelSizeGeneralModulus 1 1 (p ^ 2) [p ^ 2] := by
  have hp_dvd_sq : p ∣ p ^ 2 := by
    rw [pow_two]
    exact dvd_mul_right p p
  have hfirst : killoKernelSizeGeneralModulus 1 1 (p ^ 2) [p] = p := by
    simp [killoKernelSizeGeneralModulus, Nat.gcd_eq_right hp_dvd_sq]
  have hsecond : killoKernelSizeGeneralModulus 1 1 (p ^ 2) [p ^ 2] = p ^ 2 := by
    simp [killoKernelSizeGeneralModulus]
  have hp_lt_sq : p < p ^ 2 := by
    nlinarith [hp]
  refine ⟨hfirst, hsecond, ?_⟩
  rw [hfirst, hsecond]
  exact ne_of_lt hp_lt_sq

end Omega.Zeta
