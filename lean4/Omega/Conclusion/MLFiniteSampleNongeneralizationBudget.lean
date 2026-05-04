import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-ml-finite-sample-nongeneralization-budget`. -/
theorem paper_conclusion_ml_finite_sample_nongeneralization_budget
    {Instance Transcript : Type*} (obs : Instance → Transcript) (label : Instance → Bool)
    (A : Transcript → Bool) (pInf pT : Instance) (hobs : obs pInf = obs pT)
    (hlabel : label pInf ≠ label pT) :
    A (obs pInf) ≠ label pInf ∨ A (obs pT) ≠ label pT := by
  by_cases hInf : A (obs pInf) ≠ label pInf
  · exact Or.inl hInf
  · right
    intro hT
    apply hlabel
    calc
      label pInf = A (obs pInf) := (of_not_not hInf).symm
      _ = A (obs pT) := by rw [hobs]
      _ = label pT := hT

end Omega.Conclusion
