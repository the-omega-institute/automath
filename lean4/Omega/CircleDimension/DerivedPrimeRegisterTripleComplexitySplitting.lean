import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.CircleDimension.DerivedCofinalPrimeSupportUnboundedLedgerRank
import Omega.CircleDimension.GodelPrimeBitlengthLowerBound
import Omega.CircleDimension.ImplementationStructuralHalfCircleDimension

namespace Omega.CircleDimension

/-- Concrete data for the prime-register triple splitting package: cofinal prime support forces an
unbounded faithful ledger rank, and every such rank carries the standard Gödel `T log T`
bitlength lower bound. The implementation scale is read from the existing half-circle-dimension
theorem. -/
structure DerivedPrimeRegisterTripleComplexitySplittingData where
  primeSupportSize : ℕ → ℕ
  ledgerRank : ℕ → ℕ
  ledgerRank_pos : ∀ n : ℕ, 1 ≤ ledgerRank n
  cofinalPrimeSupport : ∀ C : ℕ, ∃ n : ℕ, C < primeSupportSize n
  stagewiseLowerBound : ∀ n : ℕ, primeSupportSize n ≤ ledgerRank n
  godelWitness : ∀ n : ℕ, GodelPrimeBitlengthWitness (ledgerRank n)

namespace DerivedPrimeRegisterTripleComplexitySplittingData

/-- The implementation scale is the already-proved half-circle implementation scale. -/
noncomputable def implScale (_D : DerivedPrimeRegisterTripleComplexitySplittingData) : ℝ :=
  (killo_implementation_vs_structural_half_circle_dimension_impl_dim : ℚ)

/-- Faithful homologizations have unbounded scale because the supported prime directions are
cofinal. -/
def homScaleInfinite (D : DerivedPrimeRegisterTripleComplexitySplittingData) : Prop :=
  ∀ C : ℕ, ∃ n : ℕ, C < D.ledgerRank n

/-- Every stagewise faithful ledger rank inherits the standard `T log T` Gödel bitlength bounds. -/
def superlinearBitlength (D : DerivedPrimeRegisterTripleComplexitySplittingData) : Prop :=
  ∀ n : ℕ, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    c * (D.ledgerRank n : ℝ) * Real.log (((D.ledgerRank n + 1 : ℕ) : ℝ)) ≤
      (D.godelWitness n).maxBitlength ∧
    (D.godelWitness n).maxBitlength ≤
      C * (D.ledgerRank n : ℝ) * Real.log (((D.ledgerRank n + 1 : ℕ) : ℝ))

end DerivedPrimeRegisterTripleComplexitySplittingData

open DerivedPrimeRegisterTripleComplexitySplittingData

/-- Paper label: `cor:derived-prime-register-triple-complexity-splitting`. The implementation
scale is exactly `1/2`, any faithful ledger realization has unbounded multiplicative scale, and
every such stage satisfies the standard `T log T` Gödel bitlength lower bound. -/
theorem paper_derived_prime_register_triple_complexity_splitting
    (D : DerivedPrimeRegisterTripleComplexitySplittingData) :
    D.implScale = (1 / 2 : Real) ∧ D.homScaleInfinite ∧ D.superlinearBitlength := by
  refine ⟨?_, ?_, ?_⟩
  · have himpl :
        killo_implementation_vs_structural_half_circle_dimension_impl_dim = (1 : ℚ) / (2 : ℚ) :=
      paper_killo_implementation_vs_structural_half_circle_dimension.2.2.2
    simpa [DerivedPrimeRegisterTripleComplexitySplittingData.implScale] using
      congrArg (fun q : ℚ => (q : ℝ)) himpl
  · let E : DerivedCofinalPrimeSupportUnboundedLedgerRankData :=
      { primeSupportSize := D.primeSupportSize
        ledgerRank := D.ledgerRank
        cofinalPrimeSupport := D.cofinalPrimeSupport
        stagewiseLowerBound := D.stagewiseLowerBound }
    exact (paper_derived_cofinal_prime_support_unbounded_ledger_rank E).2
  · intro n
    simpa [one_mul, mul_assoc, mul_left_comm, mul_comm,
      DerivedPrimeRegisterTripleComplexitySplittingData.superlinearBitlength] using
      paper_cdim_godel_prime_bitlength_lowerbound (D.ledgerRank n) 1
        (D.ledgerRank_pos n) (by decide) (D.godelWitness n)

end Omega.CircleDimension
