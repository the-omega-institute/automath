import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The Fannes--Audenaert style penalty used to convert a total-variation defect into a
mutual-information upper bound. -/
noncomputable def xi_godel_register_mutual_information_bound_penalty (q : ℕ) (t : ℝ) : ℝ :=
  t * Real.log (q - 1) - t * Real.log t - (1 - t) * Real.log (1 - t)

/-- Scalar wrapper for the averaged residue-class defect bound. The actual fiberwise TV/Jensen
work has already been compressed into the averaged defect, its continuity penalty, and the
monotonicity step needed to replace the average defect by the explicit cap `ε_q`. -/
structure xi_godel_register_mutual_information_bound_data where
  q : ℕ
  ambientCard : ℝ
  visibleCard : ℝ
  averageDefect : ℝ
  mutualInformation : ℝ
  mutualInformation_le_averagePenalty :
    mutualInformation ≤
      xi_godel_register_mutual_information_bound_penalty q averageDefect
  averageDefect_le_visibleRatio :
    averageDefect ≤ (q : ℝ) * visibleCard / (4 * ambientCard)
  averageDefect_le_cap :
    averageDefect ≤ 1 - 1 / q
  penalty_monotone :
    Monotone (xi_godel_register_mutual_information_bound_penalty q)

/-- The external register mutual information is controlled by the explicit defect cap
`ε_q = min(1 - 1/q, q|X|/(4|Ω|))`. -/
def xi_godel_register_mutual_information_bound_statement
    (D : xi_godel_register_mutual_information_bound_data) : Prop :=
  D.mutualInformation ≤
    xi_godel_register_mutual_information_bound_penalty D.q
      (min ((1 : ℝ) - 1 / (D.q : ℝ)) ((D.q : ℝ) * D.visibleCard / (4 * D.ambientCard)))

/-- Paper label: `thm:xi-godel-register-mutual-information-bound`. -/
theorem paper_xi_godel_register_mutual_information_bound
    (D : xi_godel_register_mutual_information_bound_data) :
    xi_godel_register_mutual_information_bound_statement D := by
  have hdefect :
      D.averageDefect ≤
        min ((1 : ℝ) - 1 / (D.q : ℝ)) ((D.q : ℝ) * D.visibleCard / (4 * D.ambientCard)) := by
    exact le_min D.averageDefect_le_cap D.averageDefect_le_visibleRatio
  exact le_trans D.mutualInformation_le_averagePenalty (D.penalty_monotone hdefect)

end Omega.Zeta
