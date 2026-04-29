import Omega.Zeta.SmithPrefixSufficiency

open scoped BigOperators

namespace Omega.Conclusion

/--
The Smith prefix profile has positive support at some positive depth exactly when at least one
Smith exponent is nonzero; vanishing at every depth is therefore equivalent to all exponents
being zero.

prop:conclusion-smith-bad-prime-loss-support
-/
theorem paper_conclusion_smith_bad_prime_loss_support {m : ℕ} (e : Fin m → ℕ) :
    ((∃ i, 0 < e i) ↔ ∃ k : ℕ, 1 ≤ k ∧ 0 < Omega.Zeta.smithPrefixValue e k) ∧
      ((∀ k : ℕ, Omega.Zeta.smithPrefixValue e k = 0) ↔ ∀ i, e i = 0) := by
  constructor
  · constructor
    · rintro ⟨i, hi⟩
      refine ⟨1, by omega, ?_⟩
      unfold Omega.Zeta.smithPrefixValue
      have hterm : 0 < Nat.min (e i) 1 := by
        cases h : e i with
        | zero => omega
        | succ n => simp
      have hle :
          Nat.min (e i) 1 ≤ ∑ j : Fin m, Nat.min (e j) 1 :=
        Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin m)))
          (a := i)
          (f := fun j : Fin m => Nat.min (e j) 1)
          (by intro j _; exact Nat.zero_le _)
          (by simp)
      exact lt_of_lt_of_le hterm hle
    · rintro ⟨k, _hk, hpos⟩
      by_contra hnone
      push_neg at hnone
      have hzero : ∀ i : Fin m, e i = 0 := by
        intro i
        exact Nat.eq_zero_of_le_zero (hnone i)
      have hprofile : Omega.Zeta.smithPrefixValue e k = 0 := by
        unfold Omega.Zeta.smithPrefixValue
        simp [hzero]
      omega
  · constructor
    · intro hzero i
      by_contra hi_ne
      have hi_pos : 0 < e i := Nat.pos_of_ne_zero hi_ne
      have hterm : 0 < Nat.min (e i) 1 := by
        cases h : e i with
        | zero => omega
        | succ n => simp
      have hle :
          Nat.min (e i) 1 ≤ ∑ j : Fin m, Nat.min (e j) 1 :=
        Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin m)))
          (a := i)
          (f := fun j : Fin m => Nat.min (e j) 1)
          (by intro j _; exact Nat.zero_le _)
          (by simp)
      have hprefix_pos : 0 < Omega.Zeta.smithPrefixValue e 1 := by
        unfold Omega.Zeta.smithPrefixValue
        exact lt_of_lt_of_le hterm hle
      have hkzero := hzero 1
      omega
    · intro hzero k
      unfold Omega.Zeta.smithPrefixValue
      simp [hzero]

end Omega.Conclusion
