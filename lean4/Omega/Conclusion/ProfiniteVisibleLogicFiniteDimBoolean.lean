import Mathlib.Tactic
import Omega.Conclusion.ConclusionFoldQuantumVisibleBooleanization

namespace Omega.Conclusion

/-- Concrete finite-level bookkeeping for the profinite visible-logic conclusion. -/
structure ProfiniteVisibleLogicFiniteDimBooleanData where
  visibleDimension : ℕ
  finiteLevel : ℕ
  finiteLevel_eq_visibleDimension : finiteLevel = visibleDimension

/-- The Boolean finite-level algebra on `n` visible atoms. -/
abbrev conclusion_profinite_visible_logic_finite_dim_boolean_booleanFiniteLevelAlgebra (n : ℕ) :=
  Finset (Fin n)

/-- Every finite-dimensional visible sharp-event lattice factors through the Boolean finite-level
algebra obtained from the visible subsets at the chosen finite stage. -/
def ProfiniteVisibleLogicFiniteDimBooleanStatement
    (D : ProfiniteVisibleLogicFiniteDimBooleanData) : Prop :=
  Set.range (@conclusion_fold_quantum_visible_booleanization_foldChannel D.visibleDimension) =
      conclusion_fold_quantum_visible_booleanization_visibleAlgebra D.visibleDimension ∧
    Nonempty
      ({P :
          conclusion_fold_quantum_visible_booleanization_operator D.visibleDimension //
          conclusion_fold_quantum_visible_booleanization_sharpEvent P} ≃
        conclusion_profinite_visible_logic_finite_dim_boolean_booleanFiniteLevelAlgebra
          D.finiteLevel)

/-- Paper label: `cor:conclusion-profinite-visible-logic-finite-dim-boolean`. -/
theorem paper_conclusion_profinite_visible_logic_finite_dim_boolean
    (D : ProfiniteVisibleLogicFiniteDimBooleanData) :
    ProfiniteVisibleLogicFiniteDimBooleanStatement D := by
  rcases D with ⟨n, m, hm⟩
  rcases paper_conclusion_fold_quantum_visible_booleanization n with ⟨hRange, -, hBoolean⟩
  subst hm
  exact ⟨hRange, hBoolean⟩

end Omega.Conclusion
