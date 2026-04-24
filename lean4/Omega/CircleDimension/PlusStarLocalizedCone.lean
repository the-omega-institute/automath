import Mathlib.Tactic
import Omega.CircleDimension.StarZ1sDualExtension

namespace Omega.CircleDimension

/-- The localized nonnegative cone is tracked by its finite prime support. -/
structure LocalizedNonnegativeCone where
  support : Finset ℕ

/-- Concrete model for `ℤ[1/S]_{\ge 0}` at the level needed by the paper-facing theorem. -/
def localizedNonnegativeCone (S : Finset ℕ) : LocalizedNonnegativeCone where
  support := S

/-- Extended half-circle dimension obtained from the rank-one localized dual extension. -/
noncomputable def cdimPlusStar (M : LocalizedNonnegativeCone) : ℝ :=
  (z1sStarCircleDim ⟨M.support⟩ : ℝ) / 2

/-- Paper label: `prop:cdim-plus-star-localized-cone`. -/
theorem paper_cdim_plus_star_localized_cone (S : Finset ℕ) :
    cdimPlusStar (localizedNonnegativeCone S) = (1 : ℝ) / 2 := by
  rcases paper_cdim_star_z1s_dual_extension ⟨S⟩ with ⟨_, _, hdim⟩
  simp [Z1sDualExtensionData.circleDimEqOne] at hdim
  simpa [localizedNonnegativeCone, cdimPlusStar] using
    congrArg (fun n : ℕ => (n : ℝ) / 2) hdim

end Omega.CircleDimension
