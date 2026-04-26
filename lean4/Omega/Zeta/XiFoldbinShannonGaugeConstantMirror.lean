import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-foldbin-shannon-gauge-constant-mirror`. -/
theorem paper_xi_foldbin_shannon_gauge_constant_mirror (kappa err : ℕ → ℝ)
    (phi sqrt5 : ℝ) (hconst : 1 + phi ^ 2 = phi * sqrt5)
    (hkappa : ∀ m, kappa m =
      (m : ℝ) * Real.log (2 / phi) - Real.log phi / (1 + phi ^ 2) + err m) :
    ∀ m, kappa m =
      (m : ℝ) * Real.log (2 / phi) - Real.log phi / (phi * sqrt5) + err m := by
  intro m
  simpa [hconst] using hkappa m

end Omega.Zeta
