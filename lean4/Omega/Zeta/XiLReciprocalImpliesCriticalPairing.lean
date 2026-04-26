import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-L-reciprocal-implies-critical-pairing`. -/
theorem paper_xi_l_reciprocal_implies_critical_pairing {S Z : Type*} (Xi : S → Prop)
    (qZero : Z → Prop) (toZ : S → Z) (reflect : S → S) (sharp : Z → Z)
    (hZero : ∀ s, Xi s ↔ qZero (toZ s)) (hMap : ∀ s, sharp (toZ s) = toZ (reflect s))
    (hRecip : ∀ z, qZero z → qZero (sharp z)) :
    ∀ s, Xi s → Xi (reflect s) := by
  intro s hs
  exact (hZero (reflect s)).mpr (by
    rw [← hMap s]
    exact hRecip (toZ s) ((hZero s).mp hs))

end Omega.Zeta
