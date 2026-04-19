import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Package for the rigidity statement that a solenoid isomorphism determines both the rank of the
localized additive group and its prime support. The fields encode the dual localized additive
isomorphism, the comparison of `ℚ`-ranks, the characterization of prime support by surjectivity of
the multiplication-by-`p` map, and transport of that surjectivity across the isomorphism.
    prop:cdim-solenoid-rigidity-rank-prime-support -/
structure SolenoidRigidityRankPrimeSupportData where
  sourceRank : ℕ
  targetRank : ℕ
  sourcePrimeSupport : Finset ℕ
  targetPrimeSupport : Finset ℕ
  localizedAdditiveIso : Prop
  sourceQRank : ℕ
  targetQRank : ℕ
  sourceMulByPrimeSurjective : ℕ → Prop
  targetMulByPrimeSurjective : ℕ → Prop
  localizedAdditiveIso_h : localizedAdditiveIso
  sourceQRank_eq_rank : sourceQRank = sourceRank
  targetQRank_eq_rank : targetQRank = targetRank
  qRankComparison :
    localizedAdditiveIso → sourceQRank = targetQRank
  sourcePrimeSupport_primes :
    ∀ ⦃p : ℕ⦄, p ∈ sourcePrimeSupport → Nat.Prime p
  targetPrimeSupport_primes :
    ∀ ⦃p : ℕ⦄, p ∈ targetPrimeSupport → Nat.Prime p
  sourcePrimeSupport_iff_surjective :
    ∀ p, Nat.Prime p → (p ∈ sourcePrimeSupport ↔ sourceMulByPrimeSurjective p)
  targetPrimeSupport_iff_surjective :
    ∀ p, Nat.Prime p → (p ∈ targetPrimeSupport ↔ targetMulByPrimeSurjective p)
  surjectivity_transport :
    localizedAdditiveIso →
      ∀ p, sourceMulByPrimeSurjective p ↔ targetMulByPrimeSurjective p

/-- Dualizing a solenoid isomorphism yields an isomorphism of localized additive groups. Comparing
their `ℚ`-ranks forces the ranks to agree, while the prime support is recovered from the invariant
property that multiplication by `p` is surjective.
    prop:cdim-solenoid-rigidity-rank-prime-support -/
theorem paper_cdim_solenoid_rigidity_rank_prime_support
    (D : SolenoidRigidityRankPrimeSupportData) :
    D.sourceRank = D.targetRank ∧
      D.sourcePrimeSupport = D.targetPrimeSupport := by
  have hQRank : D.sourceQRank = D.targetQRank :=
    D.qRankComparison D.localizedAdditiveIso_h
  have hRank : D.sourceRank = D.targetRank := by
    calc
      D.sourceRank = D.sourceQRank := D.sourceQRank_eq_rank.symm
      _ = D.targetQRank := hQRank
      _ = D.targetRank := D.targetQRank_eq_rank
  have hTransport :
      ∀ p, D.sourceMulByPrimeSurjective p ↔ D.targetMulByPrimeSurjective p :=
    D.surjectivity_transport D.localizedAdditiveIso_h
  have hSupport : D.sourcePrimeSupport = D.targetPrimeSupport := by
    ext p
    by_cases hp : Nat.Prime p
    · calc
        p ∈ D.sourcePrimeSupport ↔ D.sourceMulByPrimeSurjective p :=
          D.sourcePrimeSupport_iff_surjective p hp
        _ ↔ D.targetMulByPrimeSurjective p := hTransport p
        _ ↔ p ∈ D.targetPrimeSupport :=
          (D.targetPrimeSupport_iff_surjective p hp).symm
    · have hSource : p ∉ D.sourcePrimeSupport := by
        intro hpMem
        exact hp (D.sourcePrimeSupport_primes hpMem)
      have hTarget : p ∉ D.targetPrimeSupport := by
        intro hpMem
        exact hp (D.targetPrimeSupport_primes hpMem)
      simp [hSource, hTarget]
  exact ⟨hRank, hSupport⟩

end Omega.CircleDimension
