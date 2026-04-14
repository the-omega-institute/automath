import Omega.LogicExpansionChain.ChoiceSpectrum
import Omega.LogicExpansionChain.ChoiceSpectrumStandardForm

namespace Omega.LogicExpansionChain

open Classical

set_option maxHeartbeats 400000 in
/-- Paper-facing one-step criterion: distinct one-step future-image sets yield selective free will,
while universal equality of one-step future-image sets collapses the action quotient to a single
class.
    cor:logic-expansion-choice-spectrum-one-step-criterion -/
theorem paper_logic_expansion_choice_spectrum_one_step_criterion
    {Observer State Action Formula : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (Forces : Observer → State → Formula → Prop)
    (i : Observer) (p : State) :
    (((∃ α β : EnabledAction Enabled i p,
          futureImage Enabled Upd Forces i p α ≠ futureImage Enabled Upd Forces i p β) →
        HasSelectiveFreeWill (choiceSpectrum Enabled Upd Forces i p)) ∧
      ((∀ α β : EnabledAction Enabled i p,
          futureImage Enabled Upd Forces i p α = futureImage Enabled Upd Forces i p β) →
        ¬ HasSelectiveFreeWill (choiceSpectrum Enabled Upd Forces i p))) := by
  let Γ : EnabledAction Enabled i p → Set (FutureClass Enabled Upd Forces i p) :=
    futureImage Enabled Upd Forces i p
  have hsetoid :
      actionSetoid Enabled Upd Forces i p = Setoid.ker Γ := by
    ext α β
    rfl
  have hstd :
      ActionClass Enabled Upd Forces i p ≃ Set.range Γ := by
    unfold ActionClass
    rw [hsetoid]
    exact paper_logic_expansion_choice_spectrum_standard_form Γ
  constructor
  · intro hdistinct
    rcases hdistinct with ⟨α, β, hne⟩
    have hActionNontrivial : Nontrivial (ActionClass Enabled Upd Forces i p) := by
      refine ⟨hstd.symm ⟨Γ α, ⟨α, rfl⟩⟩, hstd.symm ⟨Γ β, ⟨β, rfl⟩⟩, ?_⟩
      intro hEq
      apply hne
      have hRangeEq :
          hstd (hstd.symm ⟨Γ α, ⟨α, rfl⟩⟩) = hstd (hstd.symm ⟨Γ β, ⟨β, rfl⟩⟩) :=
        congrArg hstd hEq
      have hValEq :
          (hstd (hstd.symm ⟨Γ α, ⟨α, rfl⟩⟩)).1 =
            (hstd (hstd.symm ⟨Γ β, ⟨β, rfl⟩⟩)).1 :=
        congrArg Subtype.val hRangeEq
      simpa using hValEq
    haveI : Nontrivial (ActionClass Enabled Upd Forces i p) := hActionNontrivial
    simpa [HasSelectiveFreeWill, choiceSpectrum]
  · intro hall hfree
    have hsub : Subsingleton (Set.range Γ) := by
      refine ⟨?_⟩
      intro x y
      rcases x with ⟨x, ⟨α, rfl⟩⟩
      rcases y with ⟨y, ⟨β, rfl⟩⟩
      exact Subtype.ext (hall α β)
    have hsubAction : Subsingleton (ActionClass Enabled Upd Forces i p) := by
      letI : Subsingleton (Set.range Γ) := hsub
      exact hstd.subsingleton
    exact (not_nontrivial_iff_subsingleton.mpr hsubAction) hfree

end Omega.LogicExpansionChain
