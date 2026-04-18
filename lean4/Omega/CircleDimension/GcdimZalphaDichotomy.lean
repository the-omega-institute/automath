import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Concrete seed data for the algebraic/transcendental dichotomy of `ℤ[α]`. A positive `degree`
encodes the algebraic branch, while `degree = 0` encodes the transcendental branch. -/
structure GcdimZalphaDichotomyData where
  degree : ℕ

namespace GcdimZalphaDichotomyData

/-- Rank model for the filtered pieces `⟨1, α, …, α^N⟩`. In the algebraic branch the rank is
bounded by the degree; in the transcendental branch it is exactly `N + 1`. -/
def rankAt (D : GcdimZalphaDichotomyData) (N : ℕ) : ℕ :=
  if D.degree = 0 then N + 1 else min (N + 1) D.degree

/-- Positive degree encodes the algebraic case. -/
def isAlgebraic (D : GcdimZalphaDichotomyData) : Prop :=
  0 < D.degree

/-- Vanishing degree encodes the transcendental case. -/
def isTranscendental (D : GcdimZalphaDichotomyData) : Prop :=
  D.degree = 0

/-- The algebraic branch eventually stays within the first `degree` powers. -/
def rankEventuallyBoundedByDegree (D : GcdimZalphaDichotomyData) : Prop :=
  ∀ N : ℕ, D.rankAt N ≤ D.degree

/-- The transcendental branch has exact rank `N + 1`. -/
def rankEqSucc (D : GcdimZalphaDichotomyData) : Prop :=
  ∀ N : ℕ, D.rankAt N = N + 1

/-- Growth circle dimension of the model: bounded rank gives `0`, linear growth gives `1`. -/
def growthCircleDim (D : GcdimZalphaDichotomyData) : ℕ :=
  if D.degree = 0 then 1 else 0

/-- The algebraic circle rank is the minimal-polynomial degree in the algebraic branch. -/
def algebraicCircleRank (D : GcdimZalphaDichotomyData) : ℕ :=
  D.degree

/-- The transcendental branch is encoded as infinite minimal circle rank. -/
def minCircleRankInfinite (D : GcdimZalphaDichotomyData) : Prop :=
  D.isTranscendental

end GcdimZalphaDichotomyData

open GcdimZalphaDichotomyData

private theorem rankEventuallyBoundedByDegree_of_isAlgebraic (D : GcdimZalphaDichotomyData)
    (hAlg : D.isAlgebraic) : D.rankEventuallyBoundedByDegree := by
  intro N
  have hdeg_ne : D.degree ≠ 0 := Nat.ne_of_gt hAlg
  unfold GcdimZalphaDichotomyData.rankAt
  rw [if_neg hdeg_ne]
  exact Nat.min_le_right (N + 1) D.degree

private theorem rankEqSucc_of_isTranscendental (D : GcdimZalphaDichotomyData)
    (hTrans : D.isTranscendental) : D.rankEqSucc := by
  intro N
  have hdeg : D.degree = 0 := by
    simpa [GcdimZalphaDichotomyData.isTranscendental] using hTrans
  unfold GcdimZalphaDichotomyData.rankAt
  rw [if_pos hdeg]

/-- Paper-facing algebraic/transcendental dichotomy for the one-generator subring `ℤ[α]`.
    thm:gcdim-zalpha-dichotomy -/
theorem paper_gcdim_zalpha_dichotomy (D : GcdimZalphaDichotomyData) :
    (D.isAlgebraic -> D.rankEventuallyBoundedByDegree ∧ D.growthCircleDim = 0 ∧
      D.algebraicCircleRank = D.degree) ∧
      (D.isTranscendental -> D.rankEqSucc ∧ D.growthCircleDim = 1 ∧ D.minCircleRankInfinite) := by
  refine ⟨?_, ?_⟩
  · intro hAlg
    have hdeg_ne : D.degree ≠ 0 := Nat.ne_of_gt hAlg
    refine ⟨rankEventuallyBoundedByDegree_of_isAlgebraic D hAlg, ?_, rfl⟩
    simp [GcdimZalphaDichotomyData.growthCircleDim, hdeg_ne]
  · intro hTrans
    have hdeg : D.degree = 0 := by
      simpa [GcdimZalphaDichotomyData.isTranscendental] using hTrans
    refine ⟨rankEqSucc_of_isTranscendental D hTrans, ?_, ?_⟩
    · simp [GcdimZalphaDichotomyData.growthCircleDim, hdeg]
    · exact hTrans

end Omega.CircleDimension
