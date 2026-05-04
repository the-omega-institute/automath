import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-boundary-double-forgetfulness-information-gap`. -/
theorem paper_conclusion_window6_boundary_double_forgetfulness_information_gap
    (algOrbit groupOrbit : ℕ) (hAlg : algOrbit = Nat.choose 8 3)
    (hGroup : groupOrbit = 97155) :
    algOrbit = 56 ∧ groupOrbit = 97155 ∧ algOrbit < groupOrbit := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hAlg]
    norm_num [Nat.choose]
  · exact hGroup
  · rw [hAlg, hGroup]
    norm_num [Nat.choose]

end Omega.Conclusion
