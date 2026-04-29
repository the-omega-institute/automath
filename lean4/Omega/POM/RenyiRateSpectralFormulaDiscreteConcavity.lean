import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-renyi-rate-spectral-formula-discrete-concavity`. -/
theorem paper_pom_renyi_rate_spectral_formula_discrete_concavity (E tau hR : ℕ → ℝ)
    (hE : ∀ q, 2 ≤ q → E q = (q : ℝ) * Real.log 2 - tau q)
    (htau_convex : ∀ q, 3 ≤ q → tau (q + 1) - tau q ≥ tau q - tau (q - 1))
    (hhR : ∀ q, 2 ≤ q → hR q = E q / (q - 1 : ℝ)) :
    (∀ q, 3 ≤ q → E (q + 1) - E q ≤ E q - E (q - 1)) ∧
      (∀ q, 2 ≤ q → hR q = E q / (q - 1 : ℝ)) := by
  refine ⟨?_, hhR⟩
  intro q hq
  have hq2 : 2 ≤ q := by omega
  have hqm1 : 2 ≤ q - 1 := by omega
  have hqp1 : 2 ≤ q + 1 := by omega
  rw [hE (q + 1) hqp1, hE q hq2, hE (q - 1) hqm1]
  have hconv := htau_convex q hq
  have hqm1_cast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  rw [hqm1_cast]
  norm_num [Nat.cast_add]
  nlinarith [hconv]

end Omega.POM
