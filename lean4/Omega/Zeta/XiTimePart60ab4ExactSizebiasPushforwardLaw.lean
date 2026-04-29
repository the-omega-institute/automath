import Mathlib.Tactic
import Omega.Folding.FoldBinTwoStateAsymptotic

namespace Omega.Zeta

/-- Concrete asymptotic seed used to package the exact window-`6` size-bias pushforward law
together with the already verified two-atom limit statement. -/
structure xi_time_part60ab4_exact_sizebias_pushforward_law_data where
  asymptoticSeed : Omega.Folding.FoldBinTwoStateAsymptoticData

/-- Uniform-on-output expectation against the audited window-`6` histogram `2:8, 3:4, 4:9`. -/
def xi_time_part60ab4_exact_sizebias_pushforward_law_uniform_output_expectation
    (f : ℕ → ℚ) : ℚ :=
  ((8 : ℚ) * f 2 + 4 * f 3 + 9 * f 4) / 21

/-- Microstate-pushforward expectation of the same fiber statistic. -/
def xi_time_part60ab4_exact_sizebias_pushforward_law_microstate_pushforward_expectation
    (f : ℕ → ℚ) : ℚ :=
  ((8 : ℚ) * 2 * f 2 + (4 : ℚ) * 3 * f 3 + (9 : ℚ) * 4 * f 4) / 64

/-- Exact size-bias identity for the window-`6` pushforward law, together with the first moment
and the already available two-state asymptotic package. -/
def xi_time_part60ab4_exact_sizebias_pushforward_law_statement
    (D : xi_time_part60ab4_exact_sizebias_pushforward_law_data) : Prop :=
  (∀ f : ℕ → ℚ,
    xi_time_part60ab4_exact_sizebias_pushforward_law_microstate_pushforward_expectation f =
      (21 / 64 : ℚ) *
        xi_time_part60ab4_exact_sizebias_pushforward_law_uniform_output_expectation
          (fun d => (d : ℚ) * f d)) ∧
    xi_time_part60ab4_exact_sizebias_pushforward_law_microstate_pushforward_expectation
        (fun d => d) =
      53 / 16 ∧
    D.asymptoticSeed.uniform_two_state_asymptotic ∧
    (∀ m : ℕ,
      Omega.Folding.foldBinTwoStateFiberCount m false = Omega.Folding.foldBinTwoStateGrowth ^ m + 1) ∧
    (∀ m : ℕ,
      Omega.Folding.foldBinTwoStateFiberCount m true =
        Real.goldenRatio⁻¹ * Omega.Folding.foldBinTwoStateGrowth ^ m - 1)

/-- Paper label: `thm:xi-time-part60ab4-exact-sizebias-pushforward-law`. On the audited
window-`6` fiber histogram, the microstate pushforward is exactly the size-biased version of the
uniform-on-output law, its first moment is `S₂ / S₁ = 212 / 64 = 53 / 16`, and the separate
uniform two-state asymptotic still supplies the corresponding two-state limit formulas. -/
theorem paper_xi_time_part60ab4_exact_sizebias_pushforward_law
    (D : xi_time_part60ab4_exact_sizebias_pushforward_law_data) :
    xi_time_part60ab4_exact_sizebias_pushforward_law_statement D := by
  have htwo := Omega.Folding.paper_fold_bin_two_state_asymptotic D.asymptoticSeed
  refine ⟨?_, ?_, htwo, htwo.2.1, htwo.2.2⟩
  · intro f
    unfold xi_time_part60ab4_exact_sizebias_pushforward_law_microstate_pushforward_expectation
      xi_time_part60ab4_exact_sizebias_pushforward_law_uniform_output_expectation
    norm_num
    ring
  · unfold xi_time_part60ab4_exact_sizebias_pushforward_law_microstate_pushforward_expectation
    norm_num

end Omega.Zeta
