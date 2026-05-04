import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9y-window6-visible-odd-tensor-rankone`. -/
theorem paper_xi_time_part9y_window6_visible_odd_tensor_rankone
    (O1 O3 : (Nat -> Int) -> Nat -> Int)
    (hO1 : forall f i, O1 f i = if i = 0 then f 4 - f 2 else 0)
    (hO3 : forall f i, O3 f i = if i = 0 then f 4 - f 2 else 0) :
    (forall f, (forall i, O1 f i = 0) <-> f 4 = f 2) /\
      (forall f, (forall i, O3 f i = 0) <-> f 4 = f 2) := by
  constructor
  · intro f
    constructor
    · intro hzero
      have hdiff : f 4 - f 2 = 0 := by
        simpa [hO1 f 0] using hzero 0
      exact sub_eq_zero.mp hdiff
    · intro hsame i
      by_cases hi : i = 0
      · subst i
        rw [hO1 f 0]
        simp [hsame]
      · rw [hO1 f i]
        simp [hi]
  · intro f
    constructor
    · intro hzero
      have hdiff : f 4 - f 2 = 0 := by
        simpa [hO3 f 0] using hzero 0
      exact sub_eq_zero.mp hdiff
    · intro hsame i
      by_cases hi : i = 0
      · subst i
        rw [hO3 f 0]
        simp [hsame]
      · rw [hO3 f i]
        simp [hi]

end Omega.Zeta
