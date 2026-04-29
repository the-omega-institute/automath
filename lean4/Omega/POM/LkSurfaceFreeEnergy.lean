import Mathlib.Tactic
import Omega.POM.FenceRiccatiError
import Omega.POM.ParrySurfaceDerivative

namespace Omega.POM

/-- Paper label: `cor:pom-Lk-surface-free-energy`. At the golden coupling `t = 1`, the boundary
Riccati approximants are exact determinant/Fibonacci ratios with a closed-form positive remainder,
and the surface-response coefficient matches the Parry-style factor `q / (1 + q)` together with
the specialization `t (4 + t) = 5`. -/
theorem paper_pom_lk_surface_free_energy (k : ℕ) :
    qT1 (k + 1) = (fenceDet k : ℝ) / fenceDet (k + 1) ∧
    qT1 (k + 1) = (Nat.fib (2 * k + 1) : ℝ) / Nat.fib (2 * k + 3) ∧
    qT1 k - phiInvSq =
      (1 - phiInvSq ^ 2) * phiInvSq ^ (2 * k) / (1 + phiInvSq ^ (2 * k + 1)) ∧
    0 < qT1 k - phiInvSq ∧
    phiInvSq / (1 + phiInvSq) = 1 / (phiInvSq⁻¹ + 1) ∧
    ((1 : ℝ) * (4 + 1) = 5) := by
  have hphiInvSq_pos : 0 < phiInvSq := by
    dsimp [phiInvSq]
    positivity
  rcases paper_pom_Lk_boundary_riccati_recursion_package k with
    ⟨hdet, hfib, herr, hpos⟩
  refine ⟨hdet, hfib, herr, hpos, ?_, ?_⟩
  · exact Omega.POM.ParrySurfaceDerivative.parry_surface_coupling phiInvSq
      hphiInvSq_pos
  · exact Omega.POM.ParrySurfaceDerivative.t_times_4_plus_t_at_one

end Omega.POM
