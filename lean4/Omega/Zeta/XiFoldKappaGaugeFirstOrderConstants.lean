import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.XiFoldbinGaugeDensityExactThermodynamicConstant

namespace Omega.Zeta

/-- Paper label: `thm:xi-fold-kappa-gauge-first-order-constants`. The normalized `κ` term carries
the exact constant `-(log φ) / (1 + φ²)`, while the gauge-density main term shifts it by one nat.
-/
theorem paper_xi_fold_kappa_gauge_first_order_constants (m : Nat) :
    let kappaMain := (m : Real) * Real.log (2 / Real.goldenRatio) -
      Real.log Real.goldenRatio / (1 + Real.goldenRatio ^ 2)
    let gMain := Omega.Zeta.xiFoldbinGaugeDensityThermodynamicMain m
    kappaMain - (m : Real) * Real.log (2 / Real.goldenRatio) =
        -Real.log Real.goldenRatio / (1 + Real.goldenRatio ^ 2) ∧
      gMain - (m : Real) * Real.log (2 / Real.goldenRatio) =
        -1 - Real.log Real.goldenRatio / (1 + Real.goldenRatio ^ 2) ∧
      gMain = kappaMain - 1 := by
  dsimp
  have hthermo := paper_xi_foldbin_gauge_density_exact_thermodynamic_constant m
  rcases hthermo with ⟨_hmain, hgconst, _hnonneg⟩
  constructor
  · ring
  constructor
  · simpa using hgconst
  · simp [xiFoldbinGaugeDensityThermodynamicMain]
    ring

end Omega.Zeta
