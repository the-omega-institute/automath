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

/-- Paper-facing package for short-exact additivity and the rank/rational identifications of
circle dimension.
    thm:killo-cdim-short-exact-additivity -/
theorem paper_killo_cdim_short_exact_additivity
    (rA rB rC tA tB tC rG tG : Nat) (hshort : rB = rA + rC) :
    circleDim rB tB = circleDim rA tA + circleDim rC tC ∧
      circleDim rG tG = rG ∧ ((circleDim rG tG : ℚ) = (rG : ℚ)) := by
  let f : CircleDimHomData :=
    { sourceRank := 0
      targetRank := 0
      kernelRank := 0
      imageRank := 0
      rankNullity := by simp
      imageBound := by simp }
  have hadd : circleDim rB tB = circleDim rA tA + circleDim rC tC :=
    (paper_cdim_short_exact_additivity_seeds rA rB rC tA tB tC hshort f).1
  have hrank : circleDim rG tG = rG := by
    simp [circleDim]
  have hrat : (circleDim rG tG : ℚ) = (rG : ℚ) := by
    exact_mod_cast hrank
  exact ⟨hadd, hrank, hrat⟩

/-- Paper-facing wrapper for short-exact additivity of circle dimension.
    thm:cdim-short-exact-additivity -/
theorem paper_cdim_short_exact_additivity
    (rA rB rC tA tB tC : Nat) (hshort : rB = rA + rC) :
    circleDim rB tB = circleDim rA tA + circleDim rC tC := by
  simpa using (paper_killo_cdim_short_exact_additivity rA rB rC tA tB tC 0 0 hshort).1

end Omega.CircleDimension
