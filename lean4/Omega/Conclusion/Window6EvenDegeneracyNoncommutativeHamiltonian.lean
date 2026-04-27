import Omega.Conclusion.Window6CoxeterFoldBlockNormalForm

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-even-degeneracy-noncommutative-hamiltonian`. -/
theorem paper_conclusion_window6_even_degeneracy_noncommutative_hamiltonian
    (tensorNormalForm evenAlgebraicMultiplicity : Prop)
    (hblock : conclusion_window6_coxeter_fold_block_normal_form_statement)
    (hTensor : conclusion_window6_coxeter_fold_block_normal_form_statement → tensorNormalForm)
    (hEven : tensorNormalForm → evenAlgebraicMultiplicity) :
    tensorNormalForm ∧ evenAlgebraicMultiplicity := by
  have hTensorNormalForm : tensorNormalForm := hTensor hblock
  exact ⟨hTensorNormalForm, hEven hTensorNormalForm⟩

end Omega.Conclusion
