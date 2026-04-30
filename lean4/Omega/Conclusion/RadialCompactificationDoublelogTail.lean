import Omega.Conclusion.RadialCompactificationLoglogSecondaryCost

namespace Omega.Conclusion

/-- Concrete parameters for the radial-compactification double-log tail corollary. -/
structure conclusion_radial_compactification_doublelog_tail_data where
  conclusion_radial_compactification_doublelog_tail_sigma : Real
  conclusion_radial_compactification_doublelog_tail_L : Real
  conclusion_radial_compactification_doublelog_tail_eps : Real
  conclusion_radial_compactification_doublelog_tail_bits : Nat

namespace conclusion_radial_compactification_doublelog_tail_data

/-- The away-from-critical radial coordinate used in the compactification estimate. -/
noncomputable def conclusion_radial_compactification_doublelog_tail_radialCoordinate
    (D : conclusion_radial_compactification_doublelog_tail_data) : Real :=
  (2 * D.conclusion_radial_compactification_doublelog_tail_sigma - 1) *
    Real.log D.conclusion_radial_compactification_doublelog_tail_L

/-- The bit-cost lower bound inherited from the log-log secondary-cost theorem. -/
noncomputable def conclusion_radial_compactification_doublelog_tail_cost
    (D : conclusion_radial_compactification_doublelog_tail_data) : Real :=
  Real.logb 2
    (Omega.TypedAddressBiaxialCompletion.xiJacobianAmplification
      D.conclusion_radial_compactification_doublelog_tail_radialCoordinate /
        D.conclusion_radial_compactification_doublelog_tail_eps)

end conclusion_radial_compactification_doublelog_tail_data

open conclusion_radial_compactification_doublelog_tail_data

/-- Concrete statement of the double-log tail projection: under the same off-critical certificate
as the prior log-log theorem, the radial bit cost is bounded by the certified bit budget. -/
def conclusion_radial_compactification_doublelog_tail_statement
    (D : conclusion_radial_compactification_doublelog_tail_data) : Prop :=
  D.conclusion_radial_compactification_doublelog_tail_sigma != 1 / 2 →
    1 < D.conclusion_radial_compactification_doublelog_tail_L →
      0 < D.conclusion_radial_compactification_doublelog_tail_eps →
        Omega.TypedAddressBiaxialCompletion.xiCertifiedRadialReadout
          D.conclusion_radial_compactification_doublelog_tail_radialCoordinate
          D.conclusion_radial_compactification_doublelog_tail_eps
          D.conclusion_radial_compactification_doublelog_tail_bits →
          D.conclusion_radial_compactification_doublelog_tail_cost ≤
            D.conclusion_radial_compactification_doublelog_tail_bits ∧
            ∃ radialTailCost : Real,
              radialTailCost = D.conclusion_radial_compactification_doublelog_tail_cost ∧
                radialTailCost ≤ D.conclusion_radial_compactification_doublelog_tail_bits

/-- Paper label: `cor:conclusion-radial-compactification-doublelog-tail`. -/
theorem paper_conclusion_radial_compactification_doublelog_tail
    (D : conclusion_radial_compactification_doublelog_tail_data) :
    conclusion_radial_compactification_doublelog_tail_statement D := by
  intro hsigma hL heps hcert
  have hcost :
      D.conclusion_radial_compactification_doublelog_tail_cost ≤
        D.conclusion_radial_compactification_doublelog_tail_bits := by
    simpa [conclusion_radial_compactification_doublelog_tail_cost,
      conclusion_radial_compactification_doublelog_tail_radialCoordinate]
      using paper_conclusion_radial_compactification_loglog_secondary_cost
        D.conclusion_radial_compactification_doublelog_tail_sigma
        D.conclusion_radial_compactification_doublelog_tail_L
        D.conclusion_radial_compactification_doublelog_tail_eps
        D.conclusion_radial_compactification_doublelog_tail_bits hsigma hL heps hcert
  exact ⟨hcost, ⟨D.conclusion_radial_compactification_doublelog_tail_cost, rfl, hcost⟩⟩

end Omega.Conclusion
