import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic

namespace Omega.Zeta

/-- Seed analytic predicate for the Xi-disk formalization. -/
def XiDiskAnalytic (F : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, AnalyticAt ℂ F z

/-- Concrete Adams norm used by this wrapper: the `m`-fold pointwise norm power. -/
def xiAdamsNorm (m : ℕ) (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => F z ^ m

/-- Paper label: `prop:xi-adams-norm-holomorphic`. -/
theorem paper_xi_adams_norm_holomorphic (m : ℕ) (_hm : 1 ≤ m) {F : ℂ → ℂ}
    (hF : XiDiskAnalytic F) : XiDiskAnalytic (xiAdamsNorm m F) := by
  intro z
  simpa [XiDiskAnalytic, xiAdamsNorm] using (hF z).pow m

end Omega.Zeta
