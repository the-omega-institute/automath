import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-s4-double-observable-classification`.
The fixed-point count separates the identity, transposition, three-cycle, and the two
fixed-point-free classes; the sign then separates the double transposition from the four-cycle. -/
theorem paper_conclusion_leyang_s4_double_observable_classification {Class : Type}
    (N : Class -> Nat) (eps : Class -> Int) (id trans three dbl four : Class)
    (hcover : forall c : Class, c = id ∨ c = trans ∨ c = three ∨ c = dbl ∨ c = four)
    (hid : N id = 4) (htrans : N trans = 2) (hthree : N three = 1) (hdblN : N dbl = 0)
    (hfourN : N four = 0) (hdblE : eps dbl = 1) (hfourE : eps four = -1) :
    forall c d : Class, N c = N d -> eps c = eps d -> c = d := by
  intro c d hN hE
  rcases hcover c with hc | hc | hc | hc | hc <;> subst c <;>
    rcases hcover d with hd | hd | hd | hd | hd <;> subst d <;>
    simp [hid, htrans, hthree, hdblN, hfourN, hdblE, hfourE] at hN hE ⊢

end Omega.Conclusion
