import Mathlib.Tactic

namespace Omega.Folding

/-- Paper-facing wrapper for the residue ratio of the intrinsic and cover zeta principal parts.
    prop:Ym-zeta-residue-ratio -/
theorem paper_Ym_zeta_residue_ratio
    (Rcov Rint : Real) (hcov : 0 < Rcov) (hint : 0 < Rint) (hle : Rint <= Rcov) :
    let eta : Real := Rint / Rcov
    0 < eta ∧ eta <= 1 := by
  dsimp
  refine ⟨div_pos hint hcov, ?_⟩
  exact (div_le_iff₀ hcov).2 (by simpa using hle)

end Omega.Folding
