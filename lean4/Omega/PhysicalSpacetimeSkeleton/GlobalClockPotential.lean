import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.PhysicalSpacetimeSkeleton.ClockPotentialCechCocycle

namespace Omega.PhysicalSpacetimeSkeleton

/-- If all transition constants vanish, the patchwise local potentials glue directly to a global
clock potential, and the resulting redshift factor is patch-independent.
    cor:physical-spacetime-global-clock-potential -/
theorem paper_physical_spacetime_global_clock_potential (D : ClockPotentialCechData)
    (hcompat : ∀ α β : D.Patch, D.cechConstant α β = 0) :
    ∃ φ : D.Patch → ℝ, (∀ α, φ α = D.localPotential α) ∧
      ∀ α β : D.Patch, Real.exp (-φ α) = Real.exp (-φ β) := by
  refine ⟨D.localPotential, ?_, ?_⟩
  · intro α
    rfl
  · intro α β
    have hEq : D.localPotential α = D.localPotential β := by
      have hZero := hcompat α β
      dsimp [ClockPotentialCechData.cechConstant] at hZero
      linarith
    simp [hEq]

end Omega.PhysicalSpacetimeSkeleton
