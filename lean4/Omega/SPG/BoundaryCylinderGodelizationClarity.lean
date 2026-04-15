import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.SPG.BoundaryGodelClarityExponentEquivalence
import Omega.SPG.GodelDoublelogMinkowski

namespace Omega.SPG

/-- Paper-facing arithmetic readout for boundary-cylinder Gödelization: once `log log` of the
    boundary Gödel product is identified with `log Nₘ`, the boundary dimension parameter `d`
    is read off from the cylinder-growth base `λ`, and the clarity exponent is exactly the
    existing boundary Gödel clarity exponent package.
    thm:spg-boundary-cylinder-godelization-clarity -/
theorem paper_spg_boundary_cylinder_godelization_clarity
    (d lam : ℝ) (N G ε : ℕ → ℝ)
    (hLam : 1 < lam)
    (hDoublelog : ∀ m, Real.log (Real.log (G m)) = Real.log (N m))
    (hCount : ∀ m, Real.log (N m) = d * m * Real.log lam)
    (hDecay : ∀ m, ε m = Real.exp (-((1 - d) * Real.log lam) * m)) :
    (∀ m, Real.log (Real.log (G m)) = d * m * Real.log lam) ∧
      (d < 1 ↔ ∃ gamma > 0, ∀ m, ε m ≤ Real.exp (-gamma * m)) ∧
      ∃ gamma, gamma = (1 - d) * Real.log lam := by
  have hClarity :=
    paper_spg_boundary_godel_clarity_exponent_equivalence d lam ε hLam hDecay
  refine ⟨?_, hClarity.1, hClarity.2⟩
  intro m
  rw [hDoublelog m, hCount m]

end Omega.SPG
