namespace Omega.Conclusion

/-- Concrete restriction-addition defect package.  The carry bit selects either the zero
defect or the single rank-one generator. -/
structure conclusion_foldbin_restriction_addition_rankone_defect_data where
  Domain : Type
  DefectValue : Type
  defect : Domain → Domain → DefectValue
  zeroDefect : DefectValue
  generator : DefectValue
  carry : Domain → Domain → Bool
  scale : Bool → DefectValue → DefectValue
  scale_false_generator : scale false generator = zeroDefect
  scale_true_generator : scale true generator = generator
  defect_restriction_addition_identity : ∀ x y, defect x y = scale (carry x y) generator

/-- Paper label: `prop:conclusion-foldbin-restriction-addition-rankone-defect`. -/
theorem paper_conclusion_foldbin_restriction_addition_rankone_defect
    (D : conclusion_foldbin_restriction_addition_rankone_defect_data) :
    (∀ x y, D.defect x y = D.zeroDefect ∨ D.defect x y = D.generator) ∧
      (∀ x y, D.defect x y = D.scale (D.carry x y) D.generator) := by
  constructor
  · intro x y
    cases hc : D.carry x y
    · left
      rw [D.defect_restriction_addition_identity x y, hc, D.scale_false_generator]
    · right
      rw [D.defect_restriction_addition_identity x y, hc, D.scale_true_generator]
  · exact D.defect_restriction_addition_identity

end Omega.Conclusion
