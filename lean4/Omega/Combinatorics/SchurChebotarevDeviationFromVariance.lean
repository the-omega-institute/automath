import Mathlib.Tactic

namespace Omega.Combinatorics

/-- Paper label: `cor:pom-schur-chebotarev-deviation-from-variance`. Rewriting the existing
prime-deviation estimate by the variance exponent identity gives the stated exponential form. -/
theorem paper_pom_schur_chebotarev_deviation_from_variance {ι : Type*} (Pi : ι → ℕ → ℝ)
    (Λ ρ V C : ℝ) (hC : 0 < C)
    (hdev : ∀ i N, 2 ≤ N → |Pi i N| ≤ C * Λ ^ N / (N : ℝ))
    (hV : ∀ N, Λ ^ N = Real.exp ((V / 2) * (N : ℝ))) :
    ∀ i N, 2 ≤ N → |Pi i N| ≤ C * Real.exp ((V / 2) * (N : ℝ)) / (N : ℝ) := by
  have _hrho : ρ = ρ := rfl
  have _hC : 0 < C := hC
  intro i N hN
  simpa [← hV N] using hdev i N hN

end Omega.Combinatorics
