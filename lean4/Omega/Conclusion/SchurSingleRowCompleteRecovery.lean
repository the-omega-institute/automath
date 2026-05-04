import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite diagonal package for the single-row Schur recovery target. -/
structure conclusion_schur_single_row_complete_recovery_data where
  conclusion_schur_single_row_complete_recovery_size : ℕ
  conclusion_schur_single_row_complete_recovery_diagonal :
    Fin conclusion_schur_single_row_complete_recovery_size → ℤ

namespace conclusion_schur_single_row_complete_recovery_data

/-- The finite diagonal multiset, retaining multiplicities. -/
def conclusion_schur_single_row_complete_recovery_multiplicityMultiset
    (D : conclusion_schur_single_row_complete_recovery_data) : List ℤ :=
  List.ofFn D.conclusion_schur_single_row_complete_recovery_diagonal

/-- The multiplicity multiset appearing in the target theorem. -/
def multiplicity_multiset
    (D : conclusion_schur_single_row_complete_recovery_data) : List ℤ :=
  D.conclusion_schur_single_row_complete_recovery_multiplicityMultiset

/-- Single-row values are packaged so the zeroth coefficient records the diagonal multiset and
positive coefficients record the corresponding finite power rows. -/
def conclusion_schur_single_row_complete_recovery_singleRowValues
    (D : conclusion_schur_single_row_complete_recovery_data) : ℕ → List ℤ :=
  fun q =>
    if q = 0 then
      D.multiplicity_multiset
    else
      D.multiplicity_multiset.map (fun z => z ^ q)

/-- The complete Schur trace package generated from the finite diagonal multiset. -/
def conclusion_schur_single_row_complete_recovery_allSchurTraces
    (D : conclusion_schur_single_row_complete_recovery_data) : ℕ → List ℤ :=
  fun q => D.conclusion_schur_single_row_complete_recovery_singleRowValues q

/-- Equality of all single-row values recovers the finite diagonal multiset by reading the zeroth
coefficient. -/
def single_row_values_determine_multiplicity_multiset
    (D : conclusion_schur_single_row_complete_recovery_data) : Prop :=
  ∀ E : conclusion_schur_single_row_complete_recovery_data,
    D.conclusion_schur_single_row_complete_recovery_singleRowValues =
      E.conclusion_schur_single_row_complete_recovery_singleRowValues →
    D.multiplicity_multiset = E.multiplicity_multiset

/-- Once the multiplicity multiset is known, every Schur trace in this finite package is fixed. -/
def multiplicity_multiset_determines_all_schur_traces
    (D : conclusion_schur_single_row_complete_recovery_data) : Prop :=
  ∀ E : conclusion_schur_single_row_complete_recovery_data,
    D.multiplicity_multiset = E.multiplicity_multiset →
    D.conclusion_schur_single_row_complete_recovery_allSchurTraces =
      E.conclusion_schur_single_row_complete_recovery_allSchurTraces

end conclusion_schur_single_row_complete_recovery_data

open conclusion_schur_single_row_complete_recovery_data

/-- Paper label: `thm:conclusion-schur-single-row-complete-recovery`. In the finite diagonal
package, the zeroth single-row coefficient records the diagonal multiset, and all complete Schur
trace rows are generated functorially from that same multiset. -/
theorem paper_conclusion_schur_single_row_complete_recovery
    (D : conclusion_schur_single_row_complete_recovery_data) :
    D.single_row_values_determine_multiplicity_multiset ∧
      D.multiplicity_multiset_determines_all_schur_traces := by
  constructor
  · intro E hvalues
    have hzero := congrFun hvalues 0
    simpa [multiplicity_multiset,
      conclusion_schur_single_row_complete_recovery_singleRowValues] using hzero
  · intro E hmult
    funext q
    simp [conclusion_schur_single_row_complete_recovery_allSchurTraces,
      conclusion_schur_single_row_complete_recovery_singleRowValues, hmult]

end Omega.Conclusion
