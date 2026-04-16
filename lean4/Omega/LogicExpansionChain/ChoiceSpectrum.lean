import Mathlib.Tactic

namespace Omega.LogicExpansionChain

/-- One-step successors reachable by an enabled action at state `p`. -/
def OneStepSuccessors
    {Observer State Action : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (i : Observer) (p : State) : Set State :=
  {q | ∃ α, α ∈ Enabled i p ∧ q ∈ Upd i α p}

/-- The subtype of one-step successors at `p`. -/
def OneStepFuture
    {Observer State Action : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (i : Observer) (p : State) : Type :=
  {q : State // q ∈ OneStepSuccessors Enabled Upd i p}

/-- The subtype of enabled actions at `p`. -/
def EnabledAction
    {Observer State Action : Type}
    (Enabled : Observer → State → Set Action)
    (i : Observer) (p : State) : Type :=
  {α : Action // α ∈ Enabled i p}

/-- Future-equivalence on one-step successors: two successors are equivalent when they force the
same formulas. -/
def FutureEquivalent
    {Observer State Action Formula : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (Forces : Observer → State → Formula → Prop)
    (i : Observer) (p : State) :
    OneStepFuture Enabled Upd i p → OneStepFuture Enabled Upd i p → Prop :=
  fun q r => ∀ φ, Forces i q.1 φ ↔ Forces i r.1 φ

/-- Future-equivalence is an equivalence relation. -/
theorem futureEquivalent_equivalence
    {Observer State Action Formula : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (Forces : Observer → State → Formula → Prop)
    (i : Observer) (p : State) :
    Equivalence (FutureEquivalent Enabled Upd Forces i p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q φ
    rfl
  · intro q r h φ
    exact (h φ).symm
  · intro q r s hqr hrs φ
    exact (hqr φ).trans (hrs φ)

/-- The quotient setoid on one-step successors. -/
def futureSetoid
    {Observer State Action Formula : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (Forces : Observer → State → Formula → Prop)
    (i : Observer) (p : State) :
    Setoid (OneStepFuture Enabled Upd i p) where
  r := FutureEquivalent Enabled Upd Forces i p
  iseqv := futureEquivalent_equivalence Enabled Upd Forces i p

/-- The quotient of one-step successors by future-equivalence. -/
def FutureClass
    {Observer State Action Formula : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (Forces : Observer → State → Formula → Prop)
    (i : Observer) (p : State) : Type :=
  Quotient (futureSetoid Enabled Upd Forces i p)

/-- The future-image set of an enabled action in the quotient of one-step successors. -/
def futureImage
    {Observer State Action Formula : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (Forces : Observer → State → Formula → Prop)
    (i : Observer) (p : State)
    (α : EnabledAction Enabled i p) :
    Set (FutureClass Enabled Upd Forces i p) :=
  {w | ∃ q, ∃ hq : q ∈ Upd i α.1 p,
      w = Quotient.mk (futureSetoid Enabled Upd Forces i p) ⟨q, ⟨α.1, α.2, hq⟩⟩}

/-- Action-equivalence identifies enabled actions with the same future-image set. -/
def ActionEquivalent
    {Observer State Action Formula : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (Forces : Observer → State → Formula → Prop)
    (i : Observer) (p : State) :
    EnabledAction Enabled i p → EnabledAction Enabled i p → Prop :=
  fun α β => futureImage Enabled Upd Forces i p α = futureImage Enabled Upd Forces i p β

/-- Action-equivalence is an equivalence relation. -/
theorem actionEquivalent_equivalence
    {Observer State Action Formula : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (Forces : Observer → State → Formula → Prop)
    (i : Observer) (p : State) :
    Equivalence (ActionEquivalent Enabled Upd Forces i p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro α
    rfl
  · intro α β h
    exact h.symm
  · intro α β γ hαβ hβγ
    exact hαβ.trans hβγ

/-- The quotient setoid on enabled actions. -/
def actionSetoid
    {Observer State Action Formula : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (Forces : Observer → State → Formula → Prop)
    (i : Observer) (p : State) :
    Setoid (EnabledAction Enabled i p) where
  r := ActionEquivalent Enabled Upd Forces i p
  iseqv := actionEquivalent_equivalence Enabled Upd Forces i p

/-- The quotient of enabled actions by equality of future-image sets. -/
def ActionClass
    {Observer State Action Formula : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (Forces : Observer → State → Formula → Prop)
    (i : Observer) (p : State) : Type :=
  Quotient (actionSetoid Enabled Upd Forces i p)

/-- Abstract choice-spectrum package: quotient actions, quotient futures, and the descended
future-image map. -/
structure ChoiceSpectrum where
  ActionClass : Type
  FutureClass : Type
  futureImage : ActionClass → Set FutureClass

/-- The descended future-image map on the action quotient. -/
noncomputable def quotientFutureImage
    {Observer State Action Formula : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (Forces : Observer → State → Formula → Prop)
    (i : Observer) (p : State) :
    ActionClass Enabled Upd Forces i p → Set (FutureClass Enabled Upd Forces i p) :=
  Quotient.lift
    (fun α : EnabledAction Enabled i p => futureImage Enabled Upd Forces i p α)
    (fun _ _ h => h)

/-- The quotient-based choice-spectrum structure at `p`. -/
noncomputable def choiceSpectrum
    {Observer State Action Formula : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (Forces : Observer → State → Formula → Prop)
    (i : Observer) (p : State) : ChoiceSpectrum where
  ActionClass := ActionClass Enabled Upd Forces i p
  FutureClass := FutureClass Enabled Upd Forces i p
  futureImage := quotientFutureImage Enabled Upd Forces i p

/-- The paper's selective free-will predicate: there are at least two distinct action classes. -/
def HasSelectiveFreeWill (S : ChoiceSpectrum) : Prop :=
  Nontrivial S.ActionClass

set_option maxHeartbeats 400000 in
/-- Paper-facing package: future-equivalence on one-step successors and equality of future-image
sets on enabled actions are equivalence relations, so both quotients exist and the resulting
choice-spectrum structure and its selective free-will predicate are well-defined.
    thm:logic-expansion-choice-spectrum-well-defined -/
theorem paper_logic_expansion_choice_spectrum_well_defined
    {Observer State Action Formula : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (Forces : Observer → State → Formula → Prop)
    (i : Observer) (p : State) :
    Equivalence (FutureEquivalent Enabled Upd Forces i p) ∧
      Equivalence (ActionEquivalent Enabled Upd Forces i p) ∧
      ∃ S : ChoiceSpectrum,
        S = choiceSpectrum Enabled Upd Forces i p ∧
          (HasSelectiveFreeWill S ↔
            Nontrivial (ActionClass Enabled Upd Forces i p)) := by
  refine ⟨futureEquivalent_equivalence Enabled Upd Forces i p,
    actionEquivalent_equivalence Enabled Upd Forces i p, ?_⟩
  refine ⟨choiceSpectrum Enabled Upd Forces i p, rfl, ?_⟩
  rfl

end Omega.LogicExpansionChain
