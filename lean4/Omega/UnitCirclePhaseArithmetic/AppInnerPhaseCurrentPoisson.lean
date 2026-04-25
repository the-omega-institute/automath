import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Chapter-local data for the endpoint phase-current decomposition of an inner factor: finitely
many Blaschke radii in `[0,1)` and one nonnegative singular-mass contribution. -/
structure AppInnerPhaseCurrentPoissonData where
  rootCount : ℕ
  radius : Fin rootCount → ℝ
  hradius_nonneg : ∀ j, 0 ≤ radius j
  hradius_lt_one : ∀ j, radius j < 1
  singularMass : ℝ
  hsingular_nonneg : 0 ≤ singularMass

namespace AppInnerPhaseCurrentPoissonData

/-- The single-factor endpoint Poisson current at `-1`. -/
def singlePoissonTerm (data : AppInnerPhaseCurrentPoissonData) (j : Fin data.rootCount) : ℝ :=
  (1 - data.radius j ^ 2) / (1 + data.radius j) ^ 2

/-- The finite Blaschke contribution to the endpoint phase current. -/
def blaschkeCurrent (data : AppInnerPhaseCurrentPoissonData) : ℝ :=
  ∑ j, data.singlePoissonTerm j

/-- The total endpoint phase current, including the singular measure. -/
def totalCurrent (data : AppInnerPhaseCurrentPoissonData) : ℝ :=
  data.blaschkeCurrent + data.singularMass

/-- The Poisson-kernel decomposition of the phase current. -/
def phaseCurrentMeasure (data : AppInnerPhaseCurrentPoissonData) : Prop :=
  data.totalCurrent = (∑ j, data.singlePoissonTerm j) + data.singularMass

/-- Endpoint positivity of the total current at `-1`. -/
def endpointPositivity (data : AppInnerPhaseCurrentPoissonData) : Prop :=
  0 ≤ data.totalCurrent

end AppInnerPhaseCurrentPoissonData

private lemma app_inner_phase_current_poisson_single_nonneg
    (data : AppInnerPhaseCurrentPoissonData) (j : Fin data.rootCount) :
    0 ≤ data.singlePoissonTerm j := by
  unfold AppInnerPhaseCurrentPoissonData.singlePoissonTerm
  have hsq_lt : data.radius j ^ 2 < 1 := by
    nlinarith [data.hradius_nonneg j, data.hradius_lt_one j]
  have hnum : 0 ≤ 1 - data.radius j ^ 2 := by
    linarith
  have hden : 0 ≤ (1 + data.radius j) ^ 2 := by
    positivity
  exact div_nonneg hnum hden

/-- Paper label: `thm:app-inner-phase-current-poisson`. The endpoint phase current is the sum of
the single-factor Poisson contributions together with the singular mass, and every term is
nonnegative at `-1`, so the full endpoint current is nonnegative. -/
theorem paper_app_inner_phase_current_poisson (data : AppInnerPhaseCurrentPoissonData) :
    data.phaseCurrentMeasure ∧ data.endpointPositivity := by
  refine ⟨rfl, ?_⟩
  unfold AppInnerPhaseCurrentPoissonData.endpointPositivity
    AppInnerPhaseCurrentPoissonData.totalCurrent AppInnerPhaseCurrentPoissonData.blaschkeCurrent
  refine add_nonneg ?_ data.hsingular_nonneg
  exact Finset.sum_nonneg (fun j _ => app_inner_phase_current_poisson_single_nonneg data j)

end

end Omega.UnitCirclePhaseArithmetic
