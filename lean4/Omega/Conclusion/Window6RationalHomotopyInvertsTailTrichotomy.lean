import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-rational-homotopy-inverts-tail-trichotomy`.
The triangular system on odd rational homotopy ranks is inverted by successive subtraction. -/
theorem paper_conclusion_window6_rational_homotopy_inverts_tail_trichotomy
    (n2 n3 n4 r3 r5 r7 : Nat) (hr3 : r3 = n2 + n3 + n4) (hr5 : r5 = n3 + n4)
    (hr7 : r7 = n4) : n2 = r3 - r5 ∧ n3 = r5 - r7 ∧ n4 = r7 := by
  subst r7
  subst r5
  subst r3
  omega

end Omega.Conclusion
