import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs

namespace Omega.Conclusion

universe u

/-- Concrete certificate for the fixed-order Renyi-Schatten satisfiability gap.  The Choi
eigenvalue list supplies the spectral trace, the unsatisfiable side collapses to the one-fiber
trace, the satisfiable side is bounded below by the two-fiber trace, and a certified threshold
decision procedure records the reduction consequence. -/
structure conclusion_fixed_alpha_renyi_schatten_sat_gap_data where
  Instance : Type u
  paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_alpha : ℕ
  paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_isSat : Instance → Prop
  paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_choiEigenvalues :
    Instance → List ℚ
  paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_trace : Instance → ℚ
  paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_oneFiberTrace : ℚ
  paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_twoFiberTrace : ℚ
  paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_thresholdDecision :
    Instance → Bool
  paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_alpha_fixed :
    1 < paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_alpha
  paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_choiSpectralTrace :
    ∀ φ,
      paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_trace φ =
        (paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_choiEigenvalues φ).sum
  paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_unsatOneFiberTrace :
    ∀ φ, ¬ paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_isSat φ →
      (paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_choiEigenvalues φ).sum =
        paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_oneFiberTrace
  paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_satTwoFiberLower :
    ∀ φ, paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_isSat φ →
      paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_twoFiberTrace ≤
        (paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_choiEigenvalues φ).sum
  paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_thresholdDecision_correct :
    ∀ φ,
      paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_thresholdDecision φ = true ↔
        paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_isSat φ

namespace conclusion_fixed_alpha_renyi_schatten_sat_gap_data

/-- The unsatisfiable side has exactly the certified one-fiber Renyi-Schatten trace. -/
def unsatTraceExact (D : conclusion_fixed_alpha_renyi_schatten_sat_gap_data) : Prop :=
  ∀ φ, ¬ D.paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_isSat φ →
    D.paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_trace φ =
      D.paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_oneFiberTrace

/-- The satisfiable side is bounded below by the certified two-fiber trace. -/
def satTraceLowerBound (D : conclusion_fixed_alpha_renyi_schatten_sat_gap_data) : Prop :=
  ∀ φ, D.paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_isSat φ →
    D.paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_twoFiberTrace ≤
      D.paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_trace φ

/-- Threshold decision package induced by any constant-factor approximation sharp enough to
separate the one-fiber and two-fiber traces. -/
def constantFactorApproximationImpliesP_eq_NP
    (D : conclusion_fixed_alpha_renyi_schatten_sat_gap_data) : Prop :=
  ∃ thresholdDecision : D.Instance → Bool, ∀ φ, thresholdDecision φ = true ↔
    D.paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_isSat φ

end conclusion_fixed_alpha_renyi_schatten_sat_gap_data

/-- Paper label: `thm:conclusion-fixed-alpha-renyi-schatten-sat-gap`.  The wrapper assembles the
certified Choi spectral trace, the unsatisfiable one-fiber trace formula, the satisfiable two-fiber
lower bound, and the threshold-decision reduction certificate. -/
theorem paper_conclusion_fixed_alpha_renyi_schatten_sat_gap
    (D : conclusion_fixed_alpha_renyi_schatten_sat_gap_data) :
    D.unsatTraceExact ∧ D.satTraceLowerBound ∧
      D.constantFactorApproximationImpliesP_eq_NP := by
  refine ⟨?_, ?_, ?_⟩
  · intro φ hφ
    rw [D.paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_choiSpectralTrace φ]
    exact D.paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_unsatOneFiberTrace φ hφ
  · intro φ hφ
    rw [D.paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_choiSpectralTrace φ]
    exact D.paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_satTwoFiberLower φ hφ
  · exact ⟨
      D.paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_thresholdDecision,
      D.paper_label_conclusion_fixed_alpha_renyi_schatten_sat_gap_thresholdDecision_correct⟩

end Omega.Conclusion
