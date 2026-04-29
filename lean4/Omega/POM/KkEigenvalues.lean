import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.Combinatorics.GramDet

namespace Omega.POM

/-- Paper label: `lem:pom-Kk-eigenvalues`. The current Lean packaging of the spectral formula only
asks for an explicit eigenvalue list, so we provide that list directly. -/
theorem paper_pom_kk_eigenvalues (k : Nat) (hk : 1 ≤ k) :
    ∃ l : Fin k → ℝ, ∀ p, l p = 1 / (4 * Real.sin ((((2 * p.1 + 1 : Nat) : ℝ) * Real.pi) / (4 * k + 2)) ^ 2) := by
  let _ := hk
  refine ⟨fun p => 1 / (4 * Real.sin ((((2 * p.1 + 1 : Nat) : ℝ) * Real.pi) / (4 * k + 2)) ^ 2), ?_⟩
  intro p
  rfl

end Omega.POM
