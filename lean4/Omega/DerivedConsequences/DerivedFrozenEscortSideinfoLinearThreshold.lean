import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.DerivedConsequences

/-- Paper-facing deterministic threshold statement: if the success probability is controlled by the
maximal-fiber contribution plus an off-ground-state escort tail, then the freezing-gap error adds
linearly, and any subcritical side-information budget turns the main term into an exponential
decay. -/
def derived_frozen_escort_sideinfo_linear_threshold_statement : Prop :=
  ∀ succProb topMass offMass B M ε m gap : ℝ,
    0 ≤ topMass →
    topMass ≤ 1 →
    0 ≤ offMass →
    0 < M →
    succProb ≤ topMass * min 1 ((2 : ℝ) ^ B / M) + offMass →
    offMass ≤ Real.exp (-gap) →
    ((2 : ℝ) ^ B / M) ≤ Real.exp (-ε * Real.log 2 * m) →
      succProb ≤ min 1 ((2 : ℝ) ^ B / M) + Real.exp (-gap) ∧
        succProb ≤ Real.exp (-ε * Real.log 2 * m) + Real.exp (-gap)

/-- Paper label: `thm:derived-frozen-escort-sideinfo-linear-threshold`. -/
theorem paper_derived_frozen_escort_sideinfo_linear_threshold :
    derived_frozen_escort_sideinfo_linear_threshold_statement := by
  intro succProb topMass offMass B M ε m gap htop_nonneg htop_le_one hoff_nonneg hM_pos
    hsucc hgap hbudget
  have hratio_nonneg : 0 ≤ (2 : ℝ) ^ B / M := by positivity
  have hmain_nonneg : 0 ≤ min 1 ((2 : ℝ) ^ B / M) := by
    exact le_min (by norm_num) hratio_nonneg
  have hmain :
      topMass * min 1 ((2 : ℝ) ^ B / M) ≤ min 1 ((2 : ℝ) ^ B / M) := by
    nlinarith
  have hfirst :
      succProb ≤ min 1 ((2 : ℝ) ^ B / M) + Real.exp (-gap) := by
    exact le_trans hsucc (add_le_add hmain hgap)
  refine ⟨hfirst, ?_⟩
  have hmin_le :
      min 1 ((2 : ℝ) ^ B / M) ≤ Real.exp (-ε * Real.log 2 * m) := by
    exact (min_le_right 1 ((2 : ℝ) ^ B / M)).trans hbudget
  exact le_trans hfirst (add_le_add hmin_le le_rfl)

end Omega.DerivedConsequences
