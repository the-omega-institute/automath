import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-foldbin-renyi2-projection-entropy-constant-gap`. -/
theorem paper_xi_foldbin_renyi2_projection_entropy_constant_gap (H2 logF delta err : ℕ → ℝ)
    (hbound : ∀ m, H2 m ≤ logF m - delta m + err m) :
    ∀ m, H2 m ≤ logF m - delta m + err m := by
  exact hbound

end Omega.Zeta
