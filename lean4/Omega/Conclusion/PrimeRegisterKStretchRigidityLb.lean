import Mathlib.Tactic
import Omega.Conclusion.PrimeRegisterKStretchDensityCriterion

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-prime-register-K-stretch-rigidity-lb`. -/
theorem paper_conclusion_prime_register_k_stretch_rigidity_lb
    (s t : ℕ → ℕ) (K : ℝ) (kStretchEmbedding : Prop)
    (hnecessary : kStretchEmbedding → primeFiberUpperDensity s ≤ K * primeFiberUpperDensity t)
    (hsufficient : primeFiberUpperDensity s < K * primeFiberLowerDensity t → kStretchEmbedding) :
    (kStretchEmbedding → 0 < primeFiberUpperCdim t →
      primeFiberUpperCdim s / primeFiberUpperCdim t ≤ K) ∧
      (primeFiberUpperCdim t = 0 → 0 < primeFiberUpperCdim s → ¬ kStretchEmbedding) := by
  have hcriterion :=
    paper_conclusion_prime_register_k_stretch_density_criterion
      s t K kStretchEmbedding hnecessary hsufficient
  refine ⟨?_, ?_⟩
  · intro hEmbed hposT
    have hineq : primeFiberUpperCdim s ≤ K * primeFiberUpperCdim t := hcriterion.1 hEmbed
    have hnonnegT : 0 ≤ primeFiberUpperCdim t := le_of_lt hposT
    have hneT : primeFiberUpperCdim t ≠ 0 := ne_of_gt hposT
    have hdiv :
        primeFiberUpperCdim s / primeFiberUpperCdim t ≤
          (K * primeFiberUpperCdim t) / primeFiberUpperCdim t :=
      div_le_div_of_nonneg_right hineq hnonnegT
    simpa [hneT] using hdiv
  · intro hzero hposS hEmbed
    have hineq : primeFiberUpperCdim s ≤ 0 := by
      simpa [hzero] using (hcriterion.1 hEmbed)
    exact (not_le_of_gt hposS) hineq

end Omega.Conclusion
