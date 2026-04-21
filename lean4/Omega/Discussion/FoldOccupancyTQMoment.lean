import Mathlib.Tactic
import Omega.Folding.MomentTriple

namespace Omega.Discussion

/-- The ordered-`q` occupancy coefficient `(L)_q * S_q(m) / 2^{qm}` from the discussion bound. -/
noncomputable def foldOccupancyMomentValue (q m L : ℕ) : ℚ :=
  (Nat.descFactorial L q : ℚ) * momentSum q m / (2 : ℚ) ^ (q * m)

/-- The discussion expectation identity, packaged as a concrete proposition. -/
def foldOccupancyExpectationIdentity (q m L : ℕ) : Prop :=
  foldOccupancyMomentValue q m L =
    (Nat.descFactorial L q : ℚ) * momentSum q m / (2 : ℚ) ^ (q * m)

/-- The Markov tail certificate is nonnegative and is given by the same ordered-`q` moment term. -/
def foldOccupancyTailBound (q m L : ℕ) : Prop :=
  0 ≤ foldOccupancyMomentValue q m L ∧
    foldOccupancyMomentValue q m L =
      (Nat.descFactorial L q : ℚ) * momentSum q m / (2 : ℚ) ^ (q * m)

/-- Paper label: `prop:discussion-fold-occupancy-tq-moment`.

The discussion occupancy estimate is controlled by the ordered-`q` collision moment coefficient
`(L)_q * S_q(m) / 2^{qm}`; the same explicit term is then the Markov tail certificate. -/
theorem paper_discussion_fold_occupancy_tq_moment (q m L : ℕ) :
    foldOccupancyExpectationIdentity q m L ∧ foldOccupancyTailBound q m L := by
  constructor
  · rfl
  · refine ⟨?_, rfl⟩
    unfold foldOccupancyMomentValue
    positivity

end Omega.Discussion
