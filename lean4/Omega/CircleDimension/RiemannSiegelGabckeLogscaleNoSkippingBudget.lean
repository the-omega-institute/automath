import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.CircleDimension.RiemannSiegelGabckeLogscaleOrthogonalRecursion

namespace Omega.CircleDimension

open scoped BigOperators

/-- The deleted-shell index set used in the no-skipping budget estimate. -/
def rsLogscaleDeletedShells (L : ℕ) : Finset ℕ :=
  Finset.range L

/-- The main layer-energy contribution coming from the deleted shells. -/
def rsLogscaleShellMainTerm (L : ℕ) (layerEnergy : ℕ → ℝ) : ℝ :=
  Finset.sum (rsLogscaleDeletedShells L) layerEnergy

/-- Paper-facing lower bound asserting that the initial shell energy dominates the accumulated
deleted-shell contribution up to the global cross-term budget. -/
def rsLogscaleNoSkippingBudgetConclusion
    (L : ℕ) (shellEnergy layerEnergy : ℕ → ℝ) (crossTermBudget : ℝ) : Prop :=
  shellEnergy 0 ≥ rsLogscaleShellMainTerm L layerEnergy - crossTermBudget

/-- The shellwise orthogonal recursion packages a finite-budget no-skipping estimate: once the
terminal shell energy is nonnegative, telescoping bounds the cost of deleting shells below by the
sum of the layer energies minus the global cross-term budget.
    thm:cdim-rs-logscale-no-skipping-budget -/
theorem paper_cdim_rs_logscale_no_skipping_budget
    (L : ℕ)
    (shellEnergy layerEnergy crossError shellBound : ℕ → ℝ)
    (totalShellBound : ℝ)
    (hNear : ∀ ⦃ℓ : ℕ⦄, ℓ < L → |crossError ℓ| ≤ shellBound ℓ)
    (hStep : ∀ ⦃ℓ : ℕ⦄, ℓ < L →
      shellEnergy ℓ = shellEnergy (ℓ + 1) + layerEnergy ℓ + crossError ℓ)
    (hBudget : Finset.sum (Finset.range L) shellBound ≤ totalShellBound)
    (hTerminal : 0 ≤ shellEnergy L) :
    rsLogscaleNoSkippingBudgetConclusion L shellEnergy layerEnergy totalShellBound := by
  let D : RSLogscaleOrthogonalRecursionData := {
    L := L
    shellEnergy := shellEnergy
    layerEnergy := layerEnergy
    crossError := crossError
    shellBound := shellBound
    totalShellBound := totalShellBound
    nearOrthogonalBound := hNear
    energyStep := hStep
    geometricErrorSum := hBudget
  }
  have hchain : |shellEnergy 0 - (rsLogscaleShellMainTerm L layerEnergy + shellEnergy L)| ≤
      totalShellBound := by
    simpa [D, RSLogscaleOrthogonalRecursionData.chainTelescoping, rsLogscaleShellMainTerm,
      rsLogscaleDeletedShells] using D.chainTelescoping_holds
  have hleft :
      -totalShellBound ≤ shellEnergy 0 - (rsLogscaleShellMainTerm L layerEnergy + shellEnergy L) :=
    (abs_le.mp hchain).1
  dsimp [rsLogscaleNoSkippingBudgetConclusion]
  linarith

end Omega.CircleDimension
