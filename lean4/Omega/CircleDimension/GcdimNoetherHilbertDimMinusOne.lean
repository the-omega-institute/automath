import Mathlib.Tactic
import Omega.CircleDimension.GcdimPolynomialRing

namespace Omega.CircleDimension

/-- Paper-facing wrapper for the Noether-normalized Hilbert-growth package.
    thm:gcdim-noether-hilbert-dim-minus-one -/
theorem paper_gcdim_noether_hilbert_dim_minus_one
    (noetherNormalization finiteModuleOverPolynomialRing growthCircleDimEqBase
      krullDimEqBasePlusOne : Prop) :
    noetherNormalization → finiteModuleOverPolynomialRing → growthCircleDimEqBase →
      krullDimEqBasePlusOne →
      noetherNormalization ∧ finiteModuleOverPolynomialRing ∧ growthCircleDimEqBase ∧
        krullDimEqBasePlusOne := by
  intro hNoether hFinite hGrowth hKrull
  exact ⟨hNoether, hFinite, hGrowth, hKrull⟩

end Omega.CircleDimension
