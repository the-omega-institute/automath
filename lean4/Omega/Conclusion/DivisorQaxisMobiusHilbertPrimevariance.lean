import Omega.Conclusion.DivisorCompressedQaxisHilbertBoundedness
import Omega.Conclusion.DivisorCompressedQaxisSquarerootThreshold
import Omega.Conclusion.PrimeFlatteningSupportGcdClassification
import Omega.Conclusion.RamanujanAtomicQAxisZetaStripping

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-divisor-qaxis-mobius-hilbert-primevariance`.
This conclusion assembles the Ramanujan/q-axis stripping identity, Hilbert compressed
boundedness, the visible square-root threshold, and the prime flattening equivalences. -/
theorem paper_conclusion_divisor_qaxis_mobius_hilbert_primevariance
    (atoms qs support : Finset ℕ) (C Ψ u σ : ℕ → ℂ) (s : ℕ) (ζ : ℂ)
    (hAtomic :
      ramanujanAtomicDirichletSeries atoms C s =
        (1 / ζ) * sigmaStrippingDirichletSeries support u σ)
    (hPsi : qAxisDirichletSeries qs Ψ s = sigmaStrippingDirichletSeries support u σ)
    (Dhilbert : conclusion_divisor_compressed_qaxis_hilbert_boundedness_data)
    (Dsqrt : conclusion_divisor_compressed_qaxis_squareroot_threshold_data) {p : ℕ}
    (hp : Nat.Prime p) (V : PrimeCharacterIndex p → ℂ) (F : Polynomial ℂ)
    (hCyclotomicCriterion : primeCharacterEnergy p V = 0 ↔ primeFlatteningPolynomial p F) :
    (ramanujanAtomicDirichletSeries atoms C s = (1 / ζ) * qAxisDirichletSeries qs Ψ s) ∧
      conclusion_divisor_compressed_qaxis_hilbert_boundedness_statement Dhilbert ∧
      conclusion_divisor_compressed_qaxis_sqrt_threshold_visible_statement Dsqrt ∧
      (primeFlatteningOnUnitClasses p V ↔ primeCharacterEnergy p V = 0) ∧
      (primeFlatteningPolynomial p F ↔ primeFlatteningSupportGcdDivisible p F) := by
  have hRamanujan :=
    paper_conclusion_ramanujan_atomic_qaxis_zeta_stripping atoms qs support C Ψ u σ s ζ
      hAtomic hPsi
  have hPrime :=
    paper_conclusion_prime_flattening_support_gcd_classification hp V F hCyclotomicCriterion
  exact ⟨hRamanujan.1, paper_conclusion_divisor_compressed_qaxis_hilbert_boundedness Dhilbert,
    paper_conclusion_divisor_compressed_qaxis_sqrt_threshold_visible Dsqrt, hPrime.1,
    hPrime.2.2⟩

end Omega.Conclusion
