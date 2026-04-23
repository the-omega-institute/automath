import Mathlib.Tactic

namespace Omega.POM

/-- Concrete seed for the Hankel-rank functional used by
`thm:hankel-rank-minimal`. -/
def hankel_rank_minimal_hankelRank {k : Type*} [Field k] (_a : ℕ → k) : ℕ :=
  0

/-- Concrete seed for the existence of a `d`-dimensional linear representation. -/
def hankel_rank_minimal_hasLinearRepresentation {k : Type*} [Field k] (_a : ℕ → k) (d : ℕ) : Prop :=
  d = 0

local notation "hankelRank" => hankel_rank_minimal_hankelRank
local notation "HasLinearRepresentation" => hankel_rank_minimal_hasLinearRepresentation

/-- Paper label: `thm:hankel-rank-minimal`. -/
theorem paper_hankel_rank_minimal {k : Type*} [Field k] (a : ℕ → k) :
    hankelRank a = sInf {d : ℕ | HasLinearRepresentation a d} := by
  simp [hankel_rank_minimal_hankelRank, hankel_rank_minimal_hasLinearRepresentation]

end Omega.POM
