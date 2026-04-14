import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: short exact additivity is encoded by rank additivity, and the same rank
    bookkeeping yields the rank-nullity formula for homomorphisms.
    thm:cdim-short-exact-additivity -/
theorem paper_cdim_short_exact_additivity_seeds
    (A B C tA tB tC : Nat) (hB : B = A + C) (f : CircleDimHomData) :
    circleDim B tB = circleDim A tA + circleDim C tC ∧
      circleDim f.sourceRank 0 =
        circleDim f.kernelRank 0 + circleDim f.imageRank 0 := by
  subst hB
  constructor
  · simp [circleDim]
  · exact cdim_rank_nullity f

end Omega.CircleDimension
