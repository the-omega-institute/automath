import Omega.POM.DiagonalCollapseQuadraticFreeEnergy
import Omega.POM.DiagonalSubleadingTopDegeneracy

open Filter Topology

namespace Omega.POM

/-- Paper label: `thm:pom-closure-diagonal-to-top-spectrum`. -/
theorem paper_pom_closure_diagonal_to_top_spectrum (Xcard M S : ℕ → ℝ) (tau alphaStar : ℝ)
    (D : DiagonalSubleadingTopDegeneracyData) (hTau : 0 ≤ tau)
    (hXcard_ge_one : ∀ m, 1 ≤ Xcard m)
    (hSandwich : ∀ m,
      Real.exp (((pomDiagonalMomentIndex tau m : ℝ)) * Real.log (M m)) ≤ S m ∧
        S m ≤ Xcard m * Real.exp (((pomDiagonalMomentIndex tau m : ℝ)) * Real.log (M m)))
    (hXcard : Tendsto (fun m : ℕ => Real.log (Xcard m) / (m : ℝ) ^ 2) atTop (nhds 0))
    (hM : Tendsto (fun m : ℕ => Real.log (M m) / (m : ℝ)) atTop (nhds alphaStar))
    (hq : D.q = pomDiagonalMomentIndex tau) (hTop : D.topMultiplicity = M)
    (hS : D.partitionSum = S) :
    Tendsto (pomDiagonalQuadraticFreeEnergy S) atTop (nhds (tau * alphaStar)) ∧
      D.subleadingLimit := by
  refine ⟨?_, ?_⟩
  · exact
      paper_pom_diagonal_collapse_quadratic_free_energy Xcard M S tau alphaStar hTau
        hXcard_ge_one hSandwich hXcard hM
  · simpa [DiagonalSubleadingTopDegeneracyData.subleadingLimit, hq, hTop, hS] using
      (paper_pom_diagonal_subleading_top_degeneracy D).2

end Omega.POM
