import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-infinite-prime-uniform-shadow-absolute-schur-desert`. -/
theorem paper_conclusion_infinite_prime_uniform_shadow_absolute_schur_desert
    (T : ℤ) (Good : ℕ → Prop)
    (hpos : ∀ p, Good p → 0 < p)
    (hunbounded : ∀ B : ℕ, ∃ p, Good p ∧ B < p)
    (hdiv : ∀ p, Good p → (p : ℤ) ∣ T) :
    T = 0 := by
  by_contra hT
  obtain ⟨p, hpGood, hpLarge⟩ := hunbounded T.natAbs
  obtain ⟨k, hk⟩ := hdiv p hpGood
  have hpPos : 0 < p := hpos p hpGood
  have hkNe : k ≠ 0 := by
    intro hkZero
    apply hT
    rw [hk, hkZero, mul_zero]
  have hkAbsPos : 0 < k.natAbs := Int.natAbs_pos.mpr hkNe
  have hpLeAbs : p ≤ T.natAbs := by
    rw [hk, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.le_mul_of_pos_right p hkAbsPos
  omega

end Omega.Conclusion
