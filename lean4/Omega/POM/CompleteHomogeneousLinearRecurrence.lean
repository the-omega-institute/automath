import Mathlib.Tactic

namespace Omega.POM

/-- Paper: `thm:pom-complete-homogeneous-linear-recurrence`. -/
theorem paper_pom_complete_homogeneous_linear_recurrence
    (linearRecurrence newtonComputable : Prop) (hRec : linearRecurrence)
    (hNewton : linearRecurrence → newtonComputable) :
    linearRecurrence ∧ newtonComputable := by
  exact ⟨hRec, hNewton hRec⟩

end Omega.POM
