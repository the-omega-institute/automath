import Mathlib.Tactic
import Omega.Conclusion.PrimeRegisterFiberCdimDensity

namespace Omega.Conclusion

set_option maxHeartbeats 400000 in
/-- Paper-facing `K`-stretch density criterion: once the generator-count obstruction and the
greedy matching sufficiency are available on the density side, the prime-register
half-circle-dimension normalization from
`paper_conclusion_prime_register_fiber_cdim_density` upgrades them verbatim to the `cdim`
formulation.
    thm:conclusion-prime-register-K-stretch-density-criterion -/
theorem paper_conclusion_prime_register_k_stretch_density_criterion
    (s t : ℕ → ℕ) (K : ℝ) (kStretchEmbedding : Prop)
    (hnecessary : kStretchEmbedding → primeFiberUpperDensity s ≤ K * primeFiberUpperDensity t)
    (hsufficient : primeFiberUpperDensity s < K * primeFiberLowerDensity t → kStretchEmbedding) :
    (kStretchEmbedding → primeFiberUpperCdim s ≤ K * primeFiberUpperCdim t) ∧
      (primeFiberUpperCdim s < K * primeFiberLowerCdim t → kStretchEmbedding) := by
  have hseqs : primeFiberCdimSeq s = primeFiberDensitySeq s :=
    funext (primeFiberCdimSeq_eq_densitySeq s)
  have hseqt : primeFiberCdimSeq t = primeFiberDensitySeq t :=
    funext (primeFiberCdimSeq_eq_densitySeq t)
  have hupperS : primeFiberUpperCdim s = primeFiberUpperDensity s := by
    simp [primeFiberUpperCdim, primeFiberUpperDensity, hseqs]
  have hupperT : primeFiberUpperCdim t = primeFiberUpperDensity t := by
    simp [primeFiberUpperCdim, primeFiberUpperDensity, hseqt]
  have hlowerT : primeFiberLowerCdim t = primeFiberLowerDensity t := by
    simp [primeFiberLowerCdim, primeFiberLowerDensity, hseqt]
  refine ⟨?_, ?_⟩
  · intro hEmbed
    simpa [hupperS, hupperT] using hnecessary hEmbed
  · intro hgap
    apply hsufficient
    simpa [hupperS, hlowerT] using hgap

end Omega.Conclusion
