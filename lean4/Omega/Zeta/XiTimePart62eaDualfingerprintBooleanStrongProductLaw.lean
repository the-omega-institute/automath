import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62ea-dualfingerprint-boolean-strong-product-law`.
The finite Boolean product law follows by specializing the assumed product law for
rectangular events to the requested finite events. -/
theorem paper_xi_time_part62ea_dualfingerprint_boolean_strong_product_law
    {G H : Type} [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    (deltaG : Finset G → ℚ) (deltaH : Finset H → ℚ) (deltaGH : Finset (G × H) → ℚ)
    (h_product : ∀ E F, deltaGH (E.product F) = deltaG E * deltaH F)
    (E : Finset G) (F : Finset H) :
    deltaGH (E.product F) = deltaG E * deltaH F := by
  exact h_product E F

end Omega.Zeta
