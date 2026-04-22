import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Omega.Zeta.XiComovingPrefixEndpointBarrierLaw

namespace Omega.Conclusion

open Omega.Zeta

/-- Paper label: `thm:conclusion-comoving-prefix-endpoint-twoforone-strong-frontier`. -/
theorem paper_conclusion_comoving_prefix_endpoint_twoforone_strong_frontier {T delta0 : ℝ} {B : ℕ}
    (hT : 1 ≤ T) (hdelta0 : 0 < delta0) (hdelta0_half : delta0 ≤ 1 / 2)
    (hcollision :
      (2 : ℝ) ^ B < T ^ 2 * Real.log T →
        ∃ gamma1 gamma2 : ℝ,
          gamma1 ≠ gamma2 ∧
            Nat.floor ((2 : ℝ) ^ B * ((Real.arctan gamma1) / Real.pi + 1 / 2)) =
              Nat.floor ((2 : ℝ) ^ B * ((Real.arctan gamma2) / Real.pi + 1 / 2))) :
    xiComovingPrefixPmin T delta0 B =
        Real.log (((xiComovingPrefixError T B) ^ 2 + (1 + delta0) ^ 2) / (4 * delta0)) /
          Real.log 2 ∧
      ((2 : ℝ) ^ B < T ^ 2 * Real.log T →
        ∃ gamma1 gamma2 : ℝ,
          gamma1 ≠ gamma2 ∧
            Nat.floor ((2 : ℝ) ^ B * ((Real.arctan gamma1) / Real.pi + 1 / 2)) =
              Nat.floor ((2 : ℝ) ^ B * ((Real.arctan gamma2) / Real.pi + 1 / 2))) := by
  let _ := hT
  have hbarrier := paper_xi_comoving_prefix_endpoint_barrier_law (T := T) (δ₀ := delta0) (B := B)
    hdelta0 hdelta0_half
  exact ⟨hbarrier.2, hcollision⟩

end Omega.Conclusion
