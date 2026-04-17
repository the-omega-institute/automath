import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- The seen-branch contribution in the one-shot random-labeler game. -/
def randomLabelerSeenContribution (m p : ℕ) : ℚ :=
  (p : ℚ) / (2 : ℚ) ^ m

/-- The unseen-branch contribution in the one-shot random-labeler game when the optimal
conditional success probability is bounded by `D_m / (2^m - p)`. -/
def randomLabelerUnseenContribution (m p Dm : ℕ) : ℚ :=
  (((2 ^ m - p : ℕ) : ℚ) / (2 : ℚ) ^ m) * ((Dm : ℚ) / (2 ^ m - p : ℕ))

/-- The average one-shot success upper bound obtained by splitting according to whether the query
point was already revealed among the `p` sampled sites. -/
def randomLabelerOneShotSuccessBound (m p Dm : ℕ) : ℚ :=
  randomLabelerSeenContribution m p + randomLabelerUnseenContribution m p Dm

/-- Paper label: `prop:op-algebra-random-labeler-one-shot-generalization`.
Splitting on the event that the query point has already been seen gives the exact arithmetic
upper bound `(p + D_m) / 2^m`. -/
theorem paper_op_algebra_random_labeler_one_shot_generalization
    (m p Dm : ℕ) (hp : p < 2 ^ m) :
    randomLabelerOneShotSuccessBound m p Dm = ((p + Dm : ℕ) : ℚ) / (2 : ℚ) ^ m := by
  have hpow_ne : ((2 ^ m - p : ℕ) : ℚ) ≠ 0 := by
    norm_num
    omega
  unfold randomLabelerOneShotSuccessBound
  unfold randomLabelerSeenContribution randomLabelerUnseenContribution
  field_simp [hpow_ne]
  norm_num

end Omega.OperatorAlgebra
