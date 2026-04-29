import Mathlib.Tactic

namespace Omega.POM

/-- Package the Rényi entropy gap identity as the stated duality substitution.
    cor:pom-renyi-entropy-gap-as-inf -/
theorem paper_pom_renyi_entropy_gap_as_inf (q : ℕ) (hq : 2 ≤ q) (f : ℝ → ℝ) (A : Set ℝ)
    (h tau supTerm infPenalty : ℝ) (hh : h = (q : ℝ) * Real.log 2 - tau)
    (htau : tau = supTerm) (hdual : infPenalty = (q : ℝ) * Real.log 2 - supTerm) :
    h = infPenalty := by
  have _hq := hq
  have _f := f
  have _A := A
  rw [hh, htau, hdual]

end Omega.POM
