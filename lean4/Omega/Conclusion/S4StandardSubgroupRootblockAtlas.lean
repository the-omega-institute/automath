import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-s4-standard-subgroup-rootblock-atlas`. -/
theorem paper_conclusion_s4_standard_subgroup_rootblock_atlas {Label : Type*}
    (genus : Label → ℕ) (rowOK : Label → Prop) (C2t C2d C3 C4 V4n V4m S3 D8 A4 : Label)
    (hC2t : rowOK C2t ∧ genus C2t = 19) (hC2d : rowOK C2d ∧ genus C2d = 25)
    (hC3 : rowOK C3 ∧ genus C3 = 17) (hC4 : rowOK C4 ∧ genus C4 = 13)
    (hV4n : rowOK V4n ∧ genus V4n = 13) (hV4m : rowOK V4m ∧ genus V4m = 7)
    (hS3 : rowOK S3 ∧ genus S3 = 3) (hD8 : rowOK D8 ∧ genus D8 = 4)
    (hA4 : rowOK A4 ∧ genus A4 = 5) :
    ∃ table : List Label,
      table = [C2t, C2d, C3, C4, V4n, V4m, S3, D8, A4] ∧
        (∀ H, H ∈ table → rowOK H) := by
  refine ⟨[C2t, C2d, C3, C4, V4n, V4m, S3, D8, A4], rfl, ?_⟩
  intro H hH
  simp at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hC2t.1
  · exact hC2d.1
  · exact hC3.1
  · exact hC4.1
  · exact hV4n.1
  · exact hV4m.1
  · exact hS3.1
  · exact hD8.1
  · exact hA4.1

end Omega.Conclusion
