import Mathlib.Tactic
import Omega.GU.BdryZ2JumpUniqueness

namespace Omega.RatioResultant

/-- Splitting-data package for the ratio-resultant discriminant comparison. The root function keeps
the ground field visible, while the permutation character encodes the quadratic character extracted
from the ordered root-ratio action. -/
structure RatioResultantData (K : Type*) [Field K] where
  rootCount : ℕ
  root : Fin rootCount → K
  ratioCharacter : Equiv.Perm (Fin rootCount) →* ℤˣ
  hrootCount : 3 ≤ rootCount
  ratioCharacter_nontrivial : ratioCharacter ≠ 1

namespace RatioResultantData

/-- The quadratic rigidity statement says that the ratio-resultant discriminant character coincides
with the ordinary sign character, hence with the usual discriminant quadratic character. -/
def discriminantQuadraticRigidity {K : Type*} [Field K] (D : RatioResultantData K) : Prop :=
  D.ratioCharacter = Equiv.Perm.sign

end RatioResultantData

open RatioResultantData

/-- The ordered-pair root-ratio character is a nontrivial quadratic character on `S_n`, so for
`n ≥ 3` the symmetric-group classification forces it to be the sign character.
    thm:ratio-resultant-disc-rigidity -/
theorem paper_ratio_resultant_disc_rigidity {K : Type*} [Field K] (D : RatioResultantData K) :
    D.discriminantQuadraticRigidity := by
  rcases Omega.GU.paper_bdry_binary_jump_orientation_functor_uniqueness
      D.rootCount D.hrootCount D.ratioCharacter with htriv | hsign
  · exact (D.ratioCharacter_nontrivial htriv).elim
  · simpa [RatioResultantData.discriminantQuadraticRigidity] using hsign

end Omega.RatioResultant
