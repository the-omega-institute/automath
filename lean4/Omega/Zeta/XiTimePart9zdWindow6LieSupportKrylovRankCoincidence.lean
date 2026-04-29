import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zd-window6-lie-support-krylov-rank-coincidence`.
The audited Spin(7) rank, support cardinality, and three-step Krylov rank all rewrite to `3`. -/
theorem paper_xi_time_part9zd_window6_lie_support_krylov_rank_coincidence
    (spinRank supportCard krylovRank : ℕ) (hSpin : spinRank = 3)
    (hSupport : supportCard = 3) (hKrylov : krylovRank = 3) :
    spinRank = supportCard ∧ supportCard = krylovRank ∧ krylovRank = 3 := by
  subst spinRank
  subst supportCard
  exact ⟨rfl, hKrylov.symm, hKrylov⟩

end Omega.Zeta
