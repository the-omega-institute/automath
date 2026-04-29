import Mathlib.Tactic

namespace Omega.Conclusion

/-- An integer divisible by every positive power of two is zero. -/
lemma conclusion_projective_ghost_total_integral_rigidity_eq_zero_of_all_two_powers
    (z : Int) (h : ∀ N, 1 ≤ N → (2 : Int) ^ N ∣ z) : z = 0 := by
  by_contra hz
  let a : Nat := z.natAbs
  have ha_pos : 0 < a := Int.natAbs_pos.mpr hz
  have hdvdZ : (2 : Int) ^ (a + 1) ∣ z := h (a + 1) (by omega)
  have hdvdNat : 2 ^ (a + 1) ∣ a := by
    rcases hdvdZ with ⟨k, hk⟩
    refine ⟨k.natAbs, ?_⟩
    calc
      a = z.natAbs := rfl
      _ = (((2 : Int) ^ (a + 1)) * k).natAbs := by rw [hk]
      _ = (((2 : Int) ^ (a + 1)).natAbs) * k.natAbs := by
        rw [Int.natAbs_mul]
      _ = 2 ^ (a + 1) * k.natAbs := by
        simp [Int.natAbs_pow]
  have hle : 2 ^ (a + 1) ≤ a := Nat.le_of_dvd ha_pos hdvdNat
  exact (not_le_of_gt (Nat.lt_trans (Nat.lt_succ_self a) (a + 1).lt_two_pow_self)) hle

/-- Paper label: `thm:conclusion-projective-ghost-total-integral-rigidity`. -/
theorem paper_conclusion_projective_ghost_total_integral_rigidity
    (PrimeLike : Nat → Prop) (Q Q' : Nat → Int) (T T' : Nat → Nat → Int)
    (hQ : ∀ j p N, PrimeLike p → 1 ≤ N → (p : Int) ^ N ∣ Q j - Q' j)
    (hT : ∀ q lam p N, PrimeLike p → 1 ≤ N → (p : Int) ^ N ∣ T q lam - T' q lam)
    (h2 : PrimeLike 2) :
    (∀ j, Q j = Q' j) ∧ (∀ q lam, T q lam = T' q lam) := by
  constructor
  · intro j
    have hzero :
        Q j - Q' j = 0 :=
      conclusion_projective_ghost_total_integral_rigidity_eq_zero_of_all_two_powers
        (Q j - Q' j) (fun N hN => hQ j 2 N h2 hN)
    omega
  · intro q lam
    have hzero :
        T q lam - T' q lam = 0 :=
      conclusion_projective_ghost_total_integral_rigidity_eq_zero_of_all_two_powers
        (T q lam - T' q lam) (fun N hN => hT q lam 2 N h2 hN)
    omega

end Omega.Conclusion
