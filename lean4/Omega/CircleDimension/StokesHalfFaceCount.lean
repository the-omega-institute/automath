import Mathlib.Tactic
import Omega.CircleDimension.SignedCircleDimension

namespace Omega.CircleDimension

/-- Surviving Stokes boundary faces on the orthant `ℝ^a × [0,∞)^b`. -/
def stokesOrthantFaceCount (b : ℕ) : ℕ := b

/-- Boundary faces of the compact cube `ℝ^a × [0,1]^b`. -/
def stokesCubeFaceCount (b : ℕ) : ℕ := 2 * b

/-- After imposing Dirichlet vanishing on the outer faces `{x_j = 1}`, only the
inner faces `{x_j = 0}` contribute. -/
def stokesDirichletInnerFaceCount (b : ℕ) : ℕ := b

set_option maxHeartbeats 400000 in
/-- Paper-facing one-sided versus two-sided Stokes face-count package:
the orthant contributes one face per nonnegative coordinate, the compact cube
has two faces per coordinate, the Dirichlet condition removes the outer half,
and the resulting half-weight rule matches the signed-orthant circle dimension.
prop:cdim-stokes-half-face-count -/
theorem paper_cdim_stokes_half_face_count :
    (∀ b : ℕ, stokesOrthantFaceCount b = b) ∧
    (∀ b : ℕ, stokesCubeFaceCount b = 2 * b) ∧
    (∀ b : ℕ, stokesDirichletInnerFaceCount b = stokesOrthantFaceCount b) ∧
    (∀ b : ℕ, (stokesDirichletInnerFaceCount b : ℚ) = (stokesCubeFaceCount b : ℚ) / 2) ∧
    (∀ u v finiteTorsion : ℕ,
      cdimSignedOrthant u v finiteTorsion =
        (u : ℚ) + (stokesDirichletInnerFaceCount v : ℚ) / 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b
    rfl
  · intro b
    rfl
  · intro b
    rfl
  · intro b
    norm_num [stokesDirichletInnerFaceCount, stokesCubeFaceCount]
  · intro u v finiteTorsion
    simpa [stokesDirichletInnerFaceCount] using
      (paper_cdim_signed_orthant_closed.1 u v finiteTorsion)

end Omega.CircleDimension
