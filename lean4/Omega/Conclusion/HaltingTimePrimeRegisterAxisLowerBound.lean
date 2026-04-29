import Mathlib.Tactic

namespace Omega.Conclusion

open scoped Classical

/-- Paper label: `cor:conclusion-halting-time-prime-register-axis-lower-bound`. -/
theorem paper_conclusion_halting_time_prime_register_axis_lower_bound
    {Omega X P : Type*} [Fintype Omega] [Fintype X] [Fintype P]
    (pi : Omega -> X) (iota : Omega -> X × P) (hiota : Function.Injective iota)
    (hproj : ∀ w, (iota w).1 = pi w) (b k E : Nat)
    (hP : Fintype.card P = (E + 1) ^ k)
    (hb : ∃ y : X, b ≤ Fintype.card {w : Omega // pi w = y}) :
    b ≤ (E + 1) ^ k := by
  classical
  rcases hb with ⟨y, hy⟩
  let fiber := {w : Omega // pi w = y}
  let toP : fiber → P := fun w => (iota w.1).2
  have htoP : Function.Injective toP := by
    intro u v huv
    apply Subtype.ext
    apply hiota
    ext
    · rw [hproj u.1, hproj v.1, u.2, v.2]
    · exact huv
  have hcard : Fintype.card fiber ≤ Fintype.card P :=
    Fintype.card_le_of_injective toP htoP
  exact hy.trans (hcard.trans_eq hP)

end Omega.Conclusion
