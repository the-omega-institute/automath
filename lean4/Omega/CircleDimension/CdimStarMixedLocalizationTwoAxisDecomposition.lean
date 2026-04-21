import Mathlib.Data.Finset.Max
import Omega.CircleDimension.FiniteLocalizationDirectsumPrimeLedgerExactSequence

namespace Omega.CircleDimension

/-- Mixed finite-prime localizations split into a torus axis of rank `r` and a finitely supported
prime-axis multiplicity profile. The maximal prime multiplicity is attained on the finite support.
    thm:cdim-star-mixed-localization-two-axis-decomposition -/
theorem paper_cdim_star_mixed_localization_two_axis_decomposition
    (L : FiniteLocalizationPrimeLedgerData) :
    ∃ m_p : Nat → Nat, ∃ k, (∀ p, p ∉ L.primeSupport → m_p p = 0) ∧
      L.compactExactSequence ∧ circleDim L.rankBookkeeping.sourceRank 0 = L.r ∧
      (∀ p, m_p p ≤ k) ∧ ∃ p ∈ L.primeSupport, m_p p = k := by
  classical
  obtain ⟨p0, hp0, hp0_max⟩ :=
    Finset.exists_max_image L.primeSupport L.m_p L.primeSupport_nonempty
  refine ⟨L.m_p, L.m_p p0, L.support_spec, L.hCompactExactSequence, ?_, ?_, ?_⟩
  · calc
      circleDim L.rankBookkeeping.sourceRank 0
          = circleDim L.rankBookkeeping.kernelRank 0 +
              circleDim L.rankBookkeeping.imageRank 0 := cdim_rank_nullity L.rankBookkeeping
      _ = 0 + L.r := by simp [L.kernelRank_eq_zero, L.imageRank_eq_r, circleDim]
      _ = L.r := by simp
  · intro p
    by_cases hp : p ∈ L.primeSupport
    · exact hp0_max p hp
    · rw [L.support_spec p hp]
      exact Nat.zero_le _
  · exact ⟨p0, hp0, rfl⟩

end Omega.CircleDimension
