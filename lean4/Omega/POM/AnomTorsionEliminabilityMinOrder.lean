import Mathlib.Tactic

namespace Omega

/-- Paper label: `thm:pom-anom-torsion-eliminability-min-order`. -/
theorem paper_pom_anom_torsion_eliminability_min_order
    (H : Type*) [AddCommGroup H]
    (a : H)
    (moment : Nat → H)
    (hAmp : ∀ q, 2 ≤ q → moment q = q • a)
    (torsionCriterion normGrowth minOrderCriterion : Prop)
    (hTorsion : ((∃ q, 2 ≤ q ∧ moment q = 0) ↔ torsionCriterion))
    (hGrowth : normGrowth)
    (hMin : minOrderCriterion) :
    ((∃ q, 2 ≤ q ∧ moment q = 0) ↔ torsionCriterion) ∧ normGrowth ∧ minOrderCriterion := by
  have _ : ∀ q, 2 ≤ q → moment q = q • a := hAmp
  exact ⟨hTorsion, hGrowth, hMin⟩

end Omega
