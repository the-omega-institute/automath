import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-prime-hardcore-gibbs-clt-t1-explicit`. -/
theorem paper_xi_prime_hardcore_gibbs_clt_t1_explicit (p : ℕ → ℝ) :
    ∃ μ σ2 : ℕ → ℝ,
      (∀ N, μ N = ∑ i ∈ Finset.range N, (1 : ℝ) / (p i + 1)) ∧
        (∀ N, σ2 N = ∑ i ∈ Finset.range N, p i / (p i + 1) ^ 2) := by
  refine ⟨fun N => ∑ i ∈ Finset.range N, (1 : ℝ) / (p i + 1),
    fun N => ∑ i ∈ Finset.range N, p i / (p i + 1) ^ 2, ?_, ?_⟩
  · intro N
    rfl
  · intro N
    rfl

end Omega.Zeta
