import Mathlib
import Omega.Conclusion.CapacityMajorizationSchurHardness
import Omega.Conclusion.CapacityOrderedSpectrumInfoNCEEquivalence
import Omega.Conclusion.Window6SemisimpleInvariantsFactorThroughCapacity

namespace Omega.Conclusion

/-- Conclusion-level data for the capacity-curve/order-holography universality package. The
ordered-spectrum side uses the pair of spectra `d,e`, while the holography side reuses the
chapter's finite-capacity reconstruction at level `m`. -/
structure conclusion_capacity_curve_order_holography_universality_Data where
  d : List ℝ
  e : List ℝ
  m : ℕ
  hm : 1 ≤ m

namespace conclusion_capacity_curve_order_holography_universality_Data

/-- Capacity-curve comparison is equivalent to the majorization order on the same spectra. -/
def majorization_capacity_equiv
    (D : conclusion_capacity_curve_order_holography_universality_Data) : Prop :=
  majorizes D.d D.e ↔ ∀ u : ℝ, capacityCurve D.d u ≤ capacityCurve D.e u

/-- The continuous/discrete capacity curve determines the ordered spectrum, and every
fiber-multiset semisimple invariant factors through the same capacity reconstruction. -/
def holographic_universality
    (D : conclusion_capacity_curve_order_holography_universality_Data) : Prop :=
  conclusion_capacity_ordered_spectrum_infonce_equivalence_statement ∧
    (1 ≤ D.m ∧
      (∀ d, window6HistogramFromCapacity window6CapacityCurve d = window6SemisimpleHistogram d) ∧
      (8 + 4 + 9 = 21 ∧ 8 * 2 + 4 * 3 + 9 * 4 = 64 ∧ 8 * 4 + 4 * 9 + 9 * 16 = 212) ∧
      (8 = 8 ∧ 4 = 4 ∧ 9 = 9) ∧
      (∀ {β : Type} (Obs : (ℕ → ℕ) → β),
        ∃ Φ : (ℕ → ℕ) → β,
          Φ window6CapacityCurve = Obs window6SemisimpleHistogram ∧
            ∀ C, Φ C = Obs (window6HistogramFromCapacity C)))

end conclusion_capacity_curve_order_holography_universality_Data

open conclusion_capacity_curve_order_holography_universality_Data

/-- Paper label: `thm:conclusion-capacity-curve-order-holography-universality`. The existing
capacity/majorization equivalence identifies the ordered spectrum with the full capacity curve,
and the previously verified reconstruction theorem shows that every window-`6` semisimple
fiber-multiset invariant factors through that same capacity data. -/
theorem paper_conclusion_capacity_curve_order_holography_universality
    (D : conclusion_capacity_curve_order_holography_universality_Data) :
    D.majorization_capacity_equiv ∧ D.holographic_universality := by
  refine ⟨?_, ?_⟩
  · simpa [conclusion_capacity_curve_order_holography_universality_Data.majorization_capacity_equiv]
      using (paper_conclusion_capacity_majorization_schur_hardness D.d D.e)
  · exact
      ⟨paper_conclusion_capacity_ordered_spectrum_infonce_equivalence,
        paper_conclusion_window6_semisimple_invariants_factor_through_capacity D.m D.hm⟩

end Omega.Conclusion
