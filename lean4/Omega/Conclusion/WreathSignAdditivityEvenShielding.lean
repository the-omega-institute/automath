import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

lemma conclusion_wreath_sign_additivity_even_shielding_cast_even {d : Nat} (hd : Even d) :
    (d : ZMod 2) = 0 := by
  rcases hd with ⟨m, rfl⟩
  rw [Nat.cast_add, ← two_mul]
  rw [show (2 : ZMod 2) = 0 by exact ZMod.natCast_self 2, zero_mul]

lemma conclusion_wreath_sign_additivity_even_shielding_cast_odd {d : Nat} (hd : Odd d) :
    (d : ZMod 2) = 1 := by
  rcases hd with ⟨m, rfl⟩
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  rw [show ((2 : Nat) : ZMod 2) = 0 by exact ZMod.natCast_self 2, zero_mul, zero_add]

/-- Paper label: `thm:conclusion-wreath-sign-additivity-even-shielding`. -/
theorem paper_conclusion_wreath_sign_additivity_even_shielding (d e : Nat)
    (inner : Fin e -> ZMod 2) (outer total : ZMod 2)
    (h : total = (∑ j, inner j) + (d : ZMod 2) * outer) :
    total = (∑ j, inner j) + (d : ZMod 2) * outer ∧
      (Even d -> total = ∑ j, inner j) ∧
        (Odd d -> total = (∑ j, inner j) + outer) := by
  refine ⟨h, ?_, ?_⟩
  · intro hd
    rw [h, conclusion_wreath_sign_additivity_even_shielding_cast_even hd]
    simp
  · intro hd
    rw [h, conclusion_wreath_sign_additivity_even_shielding_cast_odd hd]
    simp

end Omega.Conclusion
