import Mathlib.Tactic

namespace Omega.Conclusion

/-- The signed total of the multiplicity-`2` root shell in the `B₃` frame. -/
def conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_shell2 :
    ℤ × ℤ × ℤ :=
  (-1, 0, 0)

/-- The signed total of the multiplicity-`3` root shell in the `B₃` frame. -/
def conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_shell3 :
    ℤ × ℤ × ℤ :=
  (0, 0, 0)

/-- The signed total of the multiplicity-`4` root shell in the `B₃` frame. -/
def conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_shell4 :
    ℤ × ℤ × ℤ :=
  (1, 0, 0)

/-- Scalar multiplication of a shell-total vector. -/
def conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_smul
    (a : ℤ) (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (a * v.1, a * v.2.1, a * v.2.2)

/-- Addition of shell-total vectors. -/
def conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_add
    (u v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (u.1 + v.1, u.2.1 + v.2.1, u.2.2 + v.2.2)

/-- The first-moment vector obtained by weighting the multiplicity-`2`, `3`, and `4` shells by
`f2`, `f3`, and `f4`. -/
def conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_moment
    (f2 f3 f4 : ℤ) : ℤ × ℤ × ℤ :=
  conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_add
    (conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_smul f2
      conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_shell2)
    (conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_add
      (conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_smul f3
        conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_shell3)
      (conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_smul f4
        conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_shell4))

/-- The first moment collapses to the `e₁` axis with `e₂` and `e₃` coordinates cancelling. -/
def conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_statement
    (f2 f3 f4 : ℤ) : Prop :=
  conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_moment f2 f3 f4 =
    (f4 - f2, 0, 0)

/-- Paper label: `thm:conclusion-window6-arbitrary-multiplicity-first-moment-axis-collapse`. The
signed shell totals are `-e₁`, `0`, and `e₁`, so any multiplicity-weighted first moment keeps only
the axial coordinate `f4 - f2`. -/
theorem paper_conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse
    (f2 f3 f4 : ℤ) :
    conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_statement f2 f3 f4 := by
  dsimp [conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_statement,
    conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_moment,
    conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_add,
    conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_smul,
    conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_shell2,
    conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_shell3,
    conclusion_window6_arbitrary_multiplicity_first_moment_axis_collapse_shell4]
  ring_nf

end Omega.Conclusion
