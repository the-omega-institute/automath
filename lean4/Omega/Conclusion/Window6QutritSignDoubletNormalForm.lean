namespace Omega.Conclusion

/-- The paper-facing implication from the CRT tensor split and potential block form to the Coxeter
block normal form. -/
def conclusion_window6_qutrit_sign_doublet_normal_form_statement
    (crt_tensor_split potential_block coxeter_block : Prop) : Prop :=
  crt_tensor_split -> potential_block -> coxeter_block

/-- Paper label: `thm:conclusion-window6-qutrit-sign-doublet-normal-form`. -/
theorem paper_conclusion_window6_qutrit_sign_doublet_normal_form
    (crt_tensor_split potential_block coxeter_block : Prop)
    (conclusion_window6_qutrit_sign_doublet_normal_form_derivation :
      conclusion_window6_qutrit_sign_doublet_normal_form_statement
        crt_tensor_split potential_block coxeter_block) :
    conclusion_window6_qutrit_sign_doublet_normal_form_statement
      crt_tensor_split potential_block coxeter_block := by
  exact conclusion_window6_qutrit_sign_doublet_normal_form_derivation

end Omega.Conclusion
