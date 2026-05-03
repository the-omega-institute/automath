import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic
import Omega.Conclusion.MixedHiddenStateFiniteAbelianClassification

namespace Omega.Conclusion

/-- Concrete finite-abelian data for the odd-order mixed hidden-state receiver. -/
structure conclusion_mixed_hidden_state_odd_order_blindness_data where
  conclusion_mixed_hidden_state_odd_order_blindness_receiver : Type*
  conclusion_mixed_hidden_state_odd_order_blindness_addCommGroup :
    AddCommGroup conclusion_mixed_hidden_state_odd_order_blindness_receiver
  conclusion_mixed_hidden_state_odd_order_blindness_fintype :
    Fintype conclusion_mixed_hidden_state_odd_order_blindness_receiver
  conclusion_mixed_hidden_state_odd_order_blindness_card_coprime_two :
    (Nat.card conclusion_mixed_hidden_state_odd_order_blindness_receiver).Coprime 2
  conclusion_mixed_hidden_state_odd_order_blindness_collision_rank : ℕ
  conclusion_mixed_hidden_state_odd_order_blindness_recorded_f2_dimension : ℕ
  conclusion_mixed_hidden_state_odd_order_blindness_visible_bit_budget : ℕ

/-- The recorded F₂-dimension criterion for whether the visible budget can separate the receiver. -/
def conclusion_mixed_hidden_state_odd_order_blindness_injection_criterion
    (D : conclusion_mixed_hidden_state_odd_order_blindness_data) : Prop :=
  D.conclusion_mixed_hidden_state_odd_order_blindness_recorded_f2_dimension ≤
    D.conclusion_mixed_hidden_state_odd_order_blindness_visible_bit_budget

/-- Odd receiver order kills the hidden `2`-torsion, so the mixed observable injects into the
ordinary receiver coordinate; the remaining criterion is exactly the recorded F₂-dimension bound. -/
def conclusion_mixed_hidden_state_odd_order_blindness_statement
    (D : conclusion_mixed_hidden_state_odd_order_blindness_data) : Prop :=
  letI : AddCommGroup D.conclusion_mixed_hidden_state_odd_order_blindness_receiver :=
    D.conclusion_mixed_hidden_state_odd_order_blindness_addCommGroup
  letI : Fintype D.conclusion_mixed_hidden_state_odd_order_blindness_receiver :=
    D.conclusion_mixed_hidden_state_odd_order_blindness_fintype
  (∀ τ : TwoTorsion D.conclusion_mixed_hidden_state_odd_order_blindness_receiver,
      τ.1 = 0) ∧
    Function.Injective
      (fun obs :
          MixedHiddenStateObservable
            D.conclusion_mixed_hidden_state_odd_order_blindness_collision_rank
            D.conclusion_mixed_hidden_state_odd_order_blindness_receiver =>
        obs.2) ∧
      (conclusion_mixed_hidden_state_odd_order_blindness_injection_criterion D ↔
        D.conclusion_mixed_hidden_state_odd_order_blindness_recorded_f2_dimension ≤
          D.conclusion_mixed_hidden_state_odd_order_blindness_visible_bit_budget)

/-- Paper label: `cor:conclusion-mixed-hidden-state-odd-order-blindness`. -/
theorem paper_conclusion_mixed_hidden_state_odd_order_blindness
    (D : conclusion_mixed_hidden_state_odd_order_blindness_data) :
    conclusion_mixed_hidden_state_odd_order_blindness_statement D := by
  letI : AddCommGroup D.conclusion_mixed_hidden_state_odd_order_blindness_receiver :=
    D.conclusion_mixed_hidden_state_odd_order_blindness_addCommGroup
  letI : Fintype D.conclusion_mixed_hidden_state_odd_order_blindness_receiver :=
    D.conclusion_mixed_hidden_state_odd_order_blindness_fintype
  have conclusion_mixed_hidden_state_odd_order_blindness_two_torsion_zero :
      ∀ τ : TwoTorsion D.conclusion_mixed_hidden_state_odd_order_blindness_receiver,
        τ.1 = 0 := by
    intro τ
    have conclusion_mixed_hidden_state_odd_order_blindness_injective_two :
        Function.Injective
          (fun x : D.conclusion_mixed_hidden_state_odd_order_blindness_receiver => 2 • x) :=
      (Nat.Coprime.nsmul_right_bijective
        (G := D.conclusion_mixed_hidden_state_odd_order_blindness_receiver)
        D.conclusion_mixed_hidden_state_odd_order_blindness_card_coprime_two).1
    apply conclusion_mixed_hidden_state_odd_order_blindness_injective_two
    simpa [two_nsmul] using τ.property
  refine ⟨conclusion_mixed_hidden_state_odd_order_blindness_two_torsion_zero, ?_, Iff.rfl⟩
  intro x y hxy
  cases x with
  | mk x_hidden x_receiver =>
    cases y with
    | mk y_hidden y_receiver =>
      simp only at hxy
      subst hxy
      congr
      ext i
      apply Subtype.ext
      calc
        (x_hidden i).1 = 0 :=
          conclusion_mixed_hidden_state_odd_order_blindness_two_torsion_zero (x_hidden i)
        _ = (y_hidden i).1 :=
          (conclusion_mixed_hidden_state_odd_order_blindness_two_torsion_zero (y_hidden i)).symm

end Omega.Conclusion
