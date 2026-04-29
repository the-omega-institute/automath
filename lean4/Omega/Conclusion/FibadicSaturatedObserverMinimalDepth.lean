import Mathlib.Tactic
import Omega.Conclusion.FibadicSaturatedObserverCofinality

namespace Omega.Conclusion

open conclusion_fibadic_saturated_observer_cofinality_data

/-- Concrete data for
`cor:conclusion-fibadic-saturated-observer-minimal-depth`.  The finite observation
is represented by an actual finite type, while the factorization depths are those
defined by the saturated-observer cofinality package. -/
structure conclusion_fibadic_saturated_observer_minimal_depth_data where
  finiteObservation : Type
  finiteObservation_fintype : Fintype finiteObservation
  finiteObservation_decidableEq : DecidableEq finiteObservation
  observer : conclusion_fibadic_saturated_observer_cofinality_data
  conductor : ℕ
  conductor_pos : 0 < conductor
  conductorFactor : ℕ
  conductorFactor_unique : ∀ M : ℕ, conductor ∣ M → M ∣ conductor → M = conductor

/-- The factorization-depth set for the observed finite Abelian quotient. -/
def conclusion_fibadic_saturated_observer_minimal_depth_factorization_depths
    (D : conclusion_fibadic_saturated_observer_minimal_depth_data) : Set ℕ :=
  {d : ℕ | D.observer.hasNaturalSurjection D.conductor d}

/-- The canonical cofinality depth `d_N`. -/
def conclusion_fibadic_saturated_observer_minimal_depth_d_N
    (D : conclusion_fibadic_saturated_observer_minimal_depth_data) : ℕ :=
  D.observer.depth D.conductor

/-- The least resolving depth selected by saturated observer cofinality. -/
def conclusion_fibadic_saturated_observer_minimal_depth_d_min
    (D : conclusion_fibadic_saturated_observer_minimal_depth_data) : ℕ :=
  D.observer.depth D.conductor

/-- The minimal observer depth is the cofinality depth attached to the unique conductor. -/
def conclusion_fibadic_saturated_observer_minimal_depth_statement
    (D : conclusion_fibadic_saturated_observer_minimal_depth_data) : Prop :=
  IsLeast (conclusion_fibadic_saturated_observer_minimal_depth_factorization_depths D)
      (conclusion_fibadic_saturated_observer_minimal_depth_d_min D) ∧
    conclusion_fibadic_saturated_observer_minimal_depth_d_min D =
      conclusion_fibadic_saturated_observer_minimal_depth_d_N D

/-- Paper label: `cor:conclusion-fibadic-saturated-observer-minimal-depth`. -/
theorem paper_conclusion_fibadic_saturated_observer_minimal_depth
    (D : conclusion_fibadic_saturated_observer_minimal_depth_data) :
    conclusion_fibadic_saturated_observer_minimal_depth_statement D := by
  have hcofinal :=
    paper_conclusion_fibadic_saturated_observer_cofinality D.observer D.conductor
      D.conductor_pos
  let depths := conclusion_fibadic_saturated_observer_minimal_depth_factorization_depths D
  have hfind_mem :
      conclusion_fibadic_saturated_observer_minimal_depth_d_min D ∈ depths := by
    simpa [depths, conclusion_fibadic_saturated_observer_minimal_depth_d_min] using hcofinal.1
  have hleast :
      IsLeast depths (conclusion_fibadic_saturated_observer_minimal_depth_d_min D) := by
    refine ⟨hfind_mem, ?_⟩
    intro e he
    simpa [conclusion_fibadic_saturated_observer_minimal_depth_d_min] using
      hcofinal.2 e (by simpa [depths] using he)
  have hdmin_le_depth :
      conclusion_fibadic_saturated_observer_minimal_depth_d_min D ≤ D.observer.depth D.conductor :=
    le_rfl
  have hdepth_le_dmin :
      D.observer.depth D.conductor ≤
        conclusion_fibadic_saturated_observer_minimal_depth_d_min D :=
    hcofinal.2 (conclusion_fibadic_saturated_observer_minimal_depth_d_min D)
      (by simpa [depths] using hfind_mem)
  refine ⟨hleast, ?_⟩
  exact le_antisymm hdmin_le_depth hdepth_le_dmin

end Omega.Conclusion
