import Mathlib.Tactic

namespace Omega.PhysicalSpacetimeSkeleton

universe u

/-- Concrete local-potential data indexed by patches. The `\v{C}`ech transition constant is the
difference of the chosen local scalar potentials. -/
structure ClockPotentialCechData where
  Patch : Type u
  localPotential : Patch → ℝ

/-- The transition constant from `β` to `α`, computed from the local potentials. -/
def ClockPotentialCechData.cechConstant (D : ClockPotentialCechData) (α β : D.Patch) : ℝ :=
  D.localPotential α - D.localPotential β

/-- The potential difference on the overlap `U_α ∩ U_β` is constant with value `c`. -/
def ClockPotentialCechData.isConstantDifference (D : ClockPotentialCechData)
    (α β : D.Patch) (c : ℝ) : Prop :=
  D.cechConstant α β = c

/-- The local-potential transition constants are constant on pairwise overlaps, and their sum on a
triple overlap vanishes by telescoping.
    thm:physical-spacetime-clock-potential-cech-cocycle -/
theorem paper_physical_spacetime_clock_potential_cech_cocycle (D : ClockPotentialCechData) :
    (∀ α β : D.Patch, ∃ c : ℝ, D.isConstantDifference α β c) ∧
      (∀ α β γ : D.Patch,
        D.cechConstant α β + D.cechConstant β γ + D.cechConstant γ α = 0) := by
  refine ⟨?_, ?_⟩
  · intro α β
    exact ⟨D.cechConstant α β, rfl⟩
  · intro α β γ
    unfold ClockPotentialCechData.cechConstant
    ring_nf

end Omega.PhysicalSpacetimeSkeleton
