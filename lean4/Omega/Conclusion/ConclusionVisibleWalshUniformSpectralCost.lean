import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete spectral-gap data for the visible Walsh lower-bound specialization.  The universal
Poincare inequality controls the full variance, and the visible Walsh energy is a subspace energy
bounded by that variance. -/
structure conclusion_visible_walsh_uniform_spectral_cost_data where
  spectralGap : ℝ
  totalVariance : ℝ
  visibleWalshEnergy : ℝ
  dirichletForm : ℝ
  hspectralGap_nonneg : 0 ≤ spectralGap
  hvisibleWalshEnergy_le_totalVariance : visibleWalshEnergy ≤ totalVariance
  hpoincareLowerBound : spectralGap * totalVariance ≤ dirichletForm

namespace conclusion_visible_walsh_uniform_spectral_cost_data

/-- The universal spectral-gap/Poincare lower bound for the ambient space. -/
def poincareLowerBound
    (D : conclusion_visible_walsh_uniform_spectral_cost_data) : Prop :=
  D.spectralGap * D.totalVariance ≤ D.dirichletForm

/-- Specializing the Poincare bound to the visible Walsh subspace gives the same uniform cost. -/
def visibleWalshLowerBound
    (D : conclusion_visible_walsh_uniform_spectral_cost_data) : Prop :=
  D.spectralGap * D.visibleWalshEnergy ≤ D.dirichletForm

end conclusion_visible_walsh_uniform_spectral_cost_data

/-- Paper label: `thm:conclusion-visible-walsh-uniform-spectral-cost`. -/
theorem paper_conclusion_visible_walsh_uniform_spectral_cost
    (D : conclusion_visible_walsh_uniform_spectral_cost_data) :
    D.poincareLowerBound ∧ D.visibleWalshLowerBound := by
  refine ⟨D.hpoincareLowerBound, ?_⟩
  exact (mul_le_mul_of_nonneg_left D.hvisibleWalshEnergy_le_totalVariance
    D.hspectralGap_nonneg).trans D.hpoincareLowerBound

end Omega.Conclusion
