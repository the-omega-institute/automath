import Mathlib.Tactic
import Omega.Conclusion.BooleanOrderIdealOnebitParityDefect

namespace Omega.Conclusion

open Omega.Zeta

/-- Concrete order-ideal input for the residual-axis dichotomy. -/
structure conclusion_boolean_orderideal_residual_axis_dichotomy_data where
  conclusion_boolean_orderideal_residual_axis_dichotomy_q : Nat
  conclusion_boolean_orderideal_residual_axis_dichotomy_I :
    Finset (Finset (Fin conclusion_boolean_orderideal_residual_axis_dichotomy_q))
  conclusion_boolean_orderideal_residual_axis_dichotomy_isOrderIdeal :
    BooleanOrderIdeal conclusion_boolean_orderideal_residual_axis_dichotomy_q
      conclusion_boolean_orderideal_residual_axis_dichotomy_I
  conclusion_boolean_orderideal_residual_axis_dichotomy_nonempty :
    conclusion_boolean_orderideal_residual_axis_dichotomy_I.Nonempty

/-- The finite residue order supplied by the one-bit parity-defect theorem. -/
def conclusion_boolean_orderideal_residual_axis_dichotomy_residue_order
    (D : conclusion_boolean_orderideal_residual_axis_dichotomy_data) : Nat :=
  conclusion_boolean_orderideal_onebit_parity_defect_cokernel_order
    D.conclusion_boolean_orderideal_residual_axis_dichotomy_I

/-- Continuous-circle/profinite-circle signature on the two finite residue objects. -/
def conclusion_boolean_orderideal_residual_axis_dichotomy_signature (n : Nat) : Nat × Nat :=
  if n = 1 then (0, 0) else if n = 2 then (0, 1) else (0, n)

/-- The Boolean order-ideal residue signature is either trivial or the single dyadic axis. -/
def conclusion_boolean_orderideal_residual_axis_dichotomy_statement
    (D : conclusion_boolean_orderideal_residual_axis_dichotomy_data) : Prop :=
  conclusion_boolean_orderideal_residual_axis_dichotomy_signature
      (conclusion_boolean_orderideal_residual_axis_dichotomy_residue_order D) = (0, 0) ∨
    conclusion_boolean_orderideal_residual_axis_dichotomy_signature
      (conclusion_boolean_orderideal_residual_axis_dichotomy_residue_order D) = (0, 1)

lemma conclusion_boolean_orderideal_residual_axis_dichotomy_signature_one :
    conclusion_boolean_orderideal_residual_axis_dichotomy_signature 1 = (0, 0) := by
  simp [conclusion_boolean_orderideal_residual_axis_dichotomy_signature]

lemma conclusion_boolean_orderideal_residual_axis_dichotomy_signature_two :
    conclusion_boolean_orderideal_residual_axis_dichotomy_signature 2 = (0, 1) := by
  simp [conclusion_boolean_orderideal_residual_axis_dichotomy_signature]

/-- Paper label: `cor:conclusion-boolean-orderideal-residual-axis-dichotomy`. -/
theorem paper_conclusion_boolean_orderideal_residual_axis_dichotomy
    (D : conclusion_boolean_orderideal_residual_axis_dichotomy_data) :
    conclusion_boolean_orderideal_residual_axis_dichotomy_statement D := by
  let q := D.conclusion_boolean_orderideal_residual_axis_dichotomy_q
  let I := D.conclusion_boolean_orderideal_residual_axis_dichotomy_I
  have hprev :=
    paper_conclusion_boolean_orderideal_onebit_parity_defect q I
      D.conclusion_boolean_orderideal_residual_axis_dichotomy_isOrderIdeal
      D.conclusion_boolean_orderideal_residual_axis_dichotomy_nonempty
  rcases hprev.2.1 with hsingleton | hrest
  · have horder := (hprev.2.2.1 hsingleton).2
    right
    simpa [conclusion_boolean_orderideal_residual_axis_dichotomy_statement,
      conclusion_boolean_orderideal_residual_axis_dichotomy_residue_order, q, I, horder] using
      conclusion_boolean_orderideal_residual_axis_dichotomy_signature_two
  · rcases hrest with hnoempty | hlarge
    · have horder := (hprev.2.2.2.1 hnoempty).2
      left
      simpa [conclusion_boolean_orderideal_residual_axis_dichotomy_statement,
        conclusion_boolean_orderideal_residual_axis_dichotomy_residue_order, q, I, horder] using
        conclusion_boolean_orderideal_residual_axis_dichotomy_signature_one
    · have horder := (hprev.2.2.2.2 hlarge).2
      right
      simpa [conclusion_boolean_orderideal_residual_axis_dichotomy_statement,
        conclusion_boolean_orderideal_residual_axis_dichotomy_residue_order, q, I, horder] using
        conclusion_boolean_orderideal_residual_axis_dichotomy_signature_two

end Omega.Conclusion
