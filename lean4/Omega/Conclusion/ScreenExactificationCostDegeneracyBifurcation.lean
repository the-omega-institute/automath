import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the exactification cost-degeneracy split.  Minimal exactifications
and spanning trees are represented by their finite subtype carriers, and the Kirchhoff
count and component-count cost identity are stored as numerical facts. -/
structure conclusion_screen_exactification_cost_degeneracy_bifurcation_data where
  conclusion_screen_exactification_cost_degeneracy_bifurcation_Exactification : Type
  conclusion_screen_exactification_cost_degeneracy_bifurcation_decEqExactification :
    DecidableEq conclusion_screen_exactification_cost_degeneracy_bifurcation_Exactification
  conclusion_screen_exactification_cost_degeneracy_bifurcation_SpanningTree : Type
  conclusion_screen_exactification_cost_degeneracy_bifurcation_decEqSpanningTree :
    DecidableEq conclusion_screen_exactification_cost_degeneracy_bifurcation_SpanningTree
  conclusion_screen_exactification_cost_degeneracy_bifurcation_minimalExactifications :
    Finset conclusion_screen_exactification_cost_degeneracy_bifurcation_Exactification
  conclusion_screen_exactification_cost_degeneracy_bifurcation_spanningTrees :
    Finset conclusion_screen_exactification_cost_degeneracy_bifurcation_SpanningTree
  conclusion_screen_exactification_cost_degeneracy_bifurcation_spanningTreeEquiv :
    {x //
        x ∈
          conclusion_screen_exactification_cost_degeneracy_bifurcation_minimalExactifications} ≃
      {t //
        t ∈ conclusion_screen_exactification_cost_degeneracy_bifurcation_spanningTrees}
  conclusion_screen_exactification_cost_degeneracy_bifurcation_tau : ℕ
  conclusion_screen_exactification_cost_degeneracy_bifurcation_cardinality :
    conclusion_screen_exactification_cost_degeneracy_bifurcation_minimalExactifications.card =
      conclusion_screen_exactification_cost_degeneracy_bifurcation_tau
  conclusion_screen_exactification_cost_degeneracy_bifurcation_cost : ℕ
  conclusion_screen_exactification_cost_degeneracy_bifurcation_components : ℕ
  conclusion_screen_exactification_cost_degeneracy_bifurcation_cost_identity :
    conclusion_screen_exactification_cost_degeneracy_bifurcation_cost =
      conclusion_screen_exactification_cost_degeneracy_bifurcation_components - 1

attribute [instance]
  conclusion_screen_exactification_cost_degeneracy_bifurcation_data.conclusion_screen_exactification_cost_degeneracy_bifurcation_decEqExactification
  conclusion_screen_exactification_cost_degeneracy_bifurcation_data.conclusion_screen_exactification_cost_degeneracy_bifurcation_decEqSpanningTree

namespace conclusion_screen_exactification_cost_degeneracy_bifurcation_data

/-- Minimal exactification completions correspond canonically to spanning trees. -/
def minimalExactificationsEquivSpanningTrees
    (D : conclusion_screen_exactification_cost_degeneracy_bifurcation_data) : Prop :=
  Nonempty
    ({x //
        x ∈
          D.conclusion_screen_exactification_cost_degeneracy_bifurcation_minimalExactifications} ≃
      {t //
        t ∈ D.conclusion_screen_exactification_cost_degeneracy_bifurcation_spanningTrees})

/-- The degeneracy count is Kirchhoff's spanning-tree count. -/
def cardinalityEqTau
    (D : conclusion_screen_exactification_cost_degeneracy_bifurcation_data) : Prop :=
  D.conclusion_screen_exactification_cost_degeneracy_bifurcation_minimalExactifications.card =
    D.conclusion_screen_exactification_cost_degeneracy_bifurcation_tau

/-- The scalar exactification cost is the component-count defect. -/
def costEqComponentsMinusOne
    (D : conclusion_screen_exactification_cost_degeneracy_bifurcation_data) : Prop :=
  D.conclusion_screen_exactification_cost_degeneracy_bifurcation_cost =
    D.conclusion_screen_exactification_cost_degeneracy_bifurcation_components - 1

end conclusion_screen_exactification_cost_degeneracy_bifurcation_data

open conclusion_screen_exactification_cost_degeneracy_bifurcation_data

/-- Paper label: `thm:conclusion-screen-exactification-cost-degeneracy-bifurcation`. -/
theorem paper_conclusion_screen_exactification_cost_degeneracy_bifurcation
    (D : conclusion_screen_exactification_cost_degeneracy_bifurcation_data) :
    D.minimalExactificationsEquivSpanningTrees ∧ D.cardinalityEqTau ∧
      D.costEqComponentsMinusOne := by
  exact
    ⟨⟨D.conclusion_screen_exactification_cost_degeneracy_bifurcation_spanningTreeEquiv⟩,
      D.conclusion_screen_exactification_cost_degeneracy_bifurcation_cardinality,
      D.conclusion_screen_exactification_cost_degeneracy_bifurcation_cost_identity⟩

end Omega.Conclusion
