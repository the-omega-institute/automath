import Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension
import Omega.Folding.KilloPrimeFreedomNonFinitizability

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-implementation-compression-hom-linearization-split`.
The implementation half-dimension collapses to the single-register value `1 / 2`, while faithful
prime-exponent bookkeeping remains impossible to realize inside any finite additive register host. -/
theorem paper_conclusion_implementation_compression_hom_linearization_split :
    Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension.implHalfCircleDim =
      (1 : ℚ) / 2 ∧
      Omega.Folding.killoPrimeExponentEmbeddingFaithful ∧
      ∀ k : ℕ, Omega.Folding.killoFiniteRegisterLinearizationObstructed k := by
  rcases Omega.Folding.paper_killo_prime_freedom_non_finitizability with
    ⟨hFaithful, hObstructed⟩
  refine ⟨?_, hFaithful, hObstructed⟩
  simpa using
    (Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension.paper_xi_finite_prime_support_multiplicative_half_circle_dimension
      1).2.1

end Omega.Conclusion
