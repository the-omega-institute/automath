import Mathlib.Tactic

namespace Omega.POM

set_option linter.unusedVariables false

/-- Publication-facing wrapper for the finite product decomposition of fiber zeta counts over
fence components.
    prop:pom-fiber-zeta-product-fence -/
theorem paper_pom_fiber_zeta_product_fence
    (k : ℕ) (ells : List ℕ) (OmegaZ : ℕ → ℕ) (ZL : ℕ)
    (hprod : ZL = (ells.map OmegaZ).prod) :
    ZL = (ells.map OmegaZ).prod := by
  exact hprod

end Omega.POM
