import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.SPG.BoundaryGodelClarityExponentEquivalence
import Omega.SPG.GodelDoublelogMinkowski

namespace Omega.SPG

/-- Paper-facing package for boundary-cylinder Gödelization: the double-log readout identifies
the boundary Gödel dimension with `d`, the cylinder count gives the linear `m * log λ` slope,
and the clarity exponent is exactly the existing boundary Gödel clarity exponent package.
    thm:spg-boundary-cylinder-godelization-clarity -/
theorem paper_spg_boundary_cylinder_godelization_clarity
    (boundaryGodelDim d lamCyl : ℝ) (N G ε : ℕ → ℝ)
    (hLam : 1 < lamCyl)
    (hDoublelogReadout : boundaryGodelDim = d)
    (hDoublelog : ∀ m, Real.log (Real.log (G m)) = Real.log (N m))
    (hCount : ∀ m, Real.log (N m) = d * m * Real.log lamCyl)
    (hDecay : ∀ m, ε m = Real.exp (-((1 - d) * Real.log lamCyl) * m)) :
    boundaryGodelDim = d ∧
      (∀ m, Real.log (Real.log (G m)) = boundaryGodelDim * m * Real.log lamCyl) ∧
      (boundaryGodelDim < 1 ↔ ∃ gamma > 0, ∀ m, ε m ≤ Real.exp (-gamma * m)) ∧
      ∃ gamma, gamma = (1 - boundaryGodelDim) * Real.log lamCyl := by
  have hClarity :=
    paper_spg_boundary_godel_clarity_exponent_equivalence d lamCyl ε hLam hDecay
  refine ⟨hDoublelogReadout, ?_, ?_, ?_⟩
  · intro m
    rw [hDoublelog m, hCount m, ← hDoublelogReadout]
  · simpa [hDoublelogReadout] using hClarity.1
  · rcases hClarity.2 with ⟨gamma, hgamma⟩
    refine ⟨gamma, ?_⟩
    simpa [hDoublelogReadout] using hgamma

end Omega.SPG
