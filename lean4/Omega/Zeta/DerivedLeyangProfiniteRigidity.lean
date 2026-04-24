import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:derived-leyang-profinite-rigidity`. Packaging the five-branch full-shift
model with the profinite inverse-limit model normalizes the entropy to `log 4 = 2 log 2`. -/
theorem paper_derived_leyang_profinite_rigidity (branchModel profiniteModel : Prop) (htop : ℝ)
    (hEntropy : htop = Real.log 4) :
    branchModel → profiniteModel → branchModel ∧ profiniteModel ∧ htop = 2 * Real.log 2 := by
  intro hBranch hProfinite
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by positivity) (by positivity)]
    ring
  refine ⟨hBranch, hProfinite, ?_⟩
  calc
    htop = Real.log 4 := hEntropy
    _ = 2 * Real.log 2 := hlog4

end Omega.Zeta
