import Mathlib.Tactic

namespace Omega.Conclusion

/-- The `S`-outside part of an integer, expressed by its prime-factor contribution. -/
def conclusion_localized_dual_b_periodic_count_s_outside_part
    (S : Finset ℕ) (n : ℕ) : ℕ :=
  ∏ p ∈ (n.primeFactors.filter fun p => p ∉ S), p ^ n.factorization p

/-- Concrete finite package for the localized fixed-point count corollary. -/
structure conclusion_localized_dual_b_periodic_count_s_outside_data where
  B : ℕ
  k : ℕ
  S : Finset ℕ
  fixedPointCount : ℕ
  kernelCount : ℕ
  fixedPointCount_eq_kernelCount : fixedPointCount = kernelCount
  kernelCount_eq_sOutside :
    kernelCount =
      conclusion_localized_dual_b_periodic_count_s_outside_part S (B ^ k - 1)

/-- The fixed-point count is the `S`-outside part of `B^k - 1`. -/
def conclusion_localized_dual_b_periodic_count_s_outside_data.claim
    (D : conclusion_localized_dual_b_periodic_count_s_outside_data) : Prop :=
  D.fixedPointCount =
    conclusion_localized_dual_b_periodic_count_s_outside_part D.S (D.B ^ D.k - 1)

/-- Paper label: `cor:conclusion-localized-dual-B-periodic-count-S-outside`. -/
theorem paper_conclusion_localized_dual_b_periodic_count_s_outside
    (D : conclusion_localized_dual_b_periodic_count_s_outside_data) : D.claim := by
  rw [conclusion_localized_dual_b_periodic_count_s_outside_data.claim,
    D.fixedPointCount_eq_kernelCount, D.kernelCount_eq_sOutside]

end Omega.Conclusion
