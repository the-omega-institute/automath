import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- Paper label: `cor:xi-theta-kernel-dyadic-zero-chain`. -/
theorem paper_xi_theta_kernel_dyadic_zero_chain (F : ℕ → ℝ → ℝ) (γ Cγ : ℝ) (K0 : ℕ)
    (tail : ℕ → ℝ)
    (hunique : ∀ K, K0 ≤ K → ∃! γK : ℝ, F K γK = 0 ∧ |γ - γK| ≤ Cγ * tail K) :
    ∃ γK : ℕ → ℝ, (∀ K, K0 ≤ K → F K (γK K) = 0) ∧
      (∀ K, K0 ≤ K → |γ - γK K| ≤ Cγ * tail K) := by
  classical
  let γK : ℕ → ℝ := fun K =>
    if hK : K0 ≤ K then Classical.choose (hunique K hK) else γ
  refine ⟨γK, ?_, ?_⟩
  · intro K hK
    dsimp [γK]
    rw [dif_pos hK]
    exact (Classical.choose_spec (hunique K hK)).1.1
  · intro K hK
    dsimp [γK]
    rw [dif_pos hK]
    exact (Classical.choose_spec (hunique K hK)).1.2

end Omega.Conclusion
