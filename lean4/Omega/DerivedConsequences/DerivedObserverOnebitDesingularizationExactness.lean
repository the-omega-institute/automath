import Mathlib.Tactic
import Omega.LogicExpansionChain.ChoiceSpectrumNoDefinableSelector
import Omega.RecursiveAddressing.FocusedNonNullReadoutCriterion
import Omega.RecursiveAddressing.ObserverIndexedNullStructural
import Omega.Zeta.NullZ2DoublecoverMinDesingularization

namespace Omega.DerivedConsequences

open Omega.LogicExpansionChain
open Omega.RecursiveAddressing
open Omega.RecursiveAddressing.FocusedNonNullReadoutCriterion
open Omega.Zeta

/-- Paper label: `thm:derived-observer-onebit-desingularization-exactness`.
The observer-side null branch propagates along the explicit orbit whenever admissibility and the
empty visible fiber persist; a symmetry swapping two distinct action classes obstructs any global
selector fixed by that symmetry; and the audited `Z/2` desingularization package supplies the
minimal two-sheet cover together with the even/odd splitting data. -/
theorem paper_derived_observer_onebit_desingularization_exactness
    {State Ref Value Observer Action Formula : Type} [DecidableEq Value]
    (Adm : State → Set Ref) (Vis : State → Ref → Set Value)
    (step : State → State) (p : State) (r : Ref)
    (hAdmOrbit : ∀ n, r ∈ Adm ((step^[n]) p))
    (hVisOrbit : ∀ n, Vis ((step^[n]) p) r = ∅)
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (Forces : Observer → State → Formula → Prop)
    (i : Observer)
    (tau : ActionClass Enabled Upd Forces i p ≃ ActionClass Enabled Upd Forces i p)
    {A B : ActionClass Enabled Upd Forces i p}
    (hAB : A ≠ B)
    (hA : tau A = B)
    (hB : tau B = A)
    {n : ℕ} (η : Fin n → Fin 2) (Bmat : Matrix (Fin n) (Fin n) ℂ) :
    (∀ k, typedReadout Adm Vis ((step^[k]) p) r = Readout.null) ∧
      (¬ ∃ choose : ActionClass Enabled Upd Forces i p,
        (choose = A ∨ choose = B) ∧ tau choose = choose) ∧
      (let D := xi_null_z2_doublecover_min_desingularization_splittingData Bmat
       D.hasDirectSumSplitting ∧
         D.determinantFactorization ∧
         (∀ v : Fin n,
            Fintype.card {y : xi_null_z2_doublecover_min_desingularization_coverVertex n //
              xi_null_z2_doublecover_min_desingularization_coverProjection y = v} = 2) ∧
         (∀ d : ℕ, 0 < d → Even d → 2 ≤ d)) := by
  have hnull :
      ∀ k, typedReadout Adm Vis ((step^[k]) p) r = Readout.null := by
    intro k
    exact
      (paper_recursive_addressing_observer_indexed_null_structural
        Adm Vis
        (p := (step^[k]) p)
        (r := r)).2
        ⟨hAdmOrbit k, hVisOrbit k⟩
  have hselector :
      ¬ ∃ choose : ActionClass Enabled Upd Forces i p,
        (choose = A ∨ choose = B) ∧ tau choose = choose := by
    exact paper_logic_expansion_choice_spectrum_no_definable_selector
      Enabled Upd Forces i p tau hAB hA hB
  have hcover := paper_xi_null_z2_doublecover_min_desingularization η Bmat
  refine ⟨hnull, hselector, ?_⟩
  exact ⟨hcover.2.2.1, hcover.2.2.2.1, hcover.2.2.2.2.1, hcover.2.2.2.2.2⟩

end Omega.DerivedConsequences
