import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Conclusion.F2BinomialBasisFromDeltaNilpotent

namespace Omega.Conclusion

open scoped fwdDiff

/-- Iterating the characteristic-`2` operator `E + 1` is the same as iterating the forward
difference `a(n + 1) + a(n)`. -/
def iteratedEPlusOneMod2 (e : Nat) (a : Nat -> ZMod 2) : Nat -> ZMod 2 :=
  Nat.iterate forwardDiff e a

@[simp] lemma iteratedEPlusOneMod2_zero (a : Nat -> ZMod 2) :
    iteratedEPlusOneMod2 0 a = a := rfl

private lemma iteratedEPlusOneMod2_pow_two :
    ∀ t (a : Nat -> ZMod 2) (m : Nat), iteratedEPlusOneMod2 (2 ^ t) a m = a (m + 2 ^ t) + a m
  | 0, a, m => by
      simp [iteratedEPlusOneMod2, Omega.Conclusion.forwardDiff, fwdDiff, sub_eq_add_neg]
  | t + 1, a, m => by
      have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by
        omega
      rw [hpow, iteratedEPlusOneMod2, Function.iterate_add_apply]
      have hfirst :
          Nat.iterate forwardDiff (2 ^ t) (Nat.iterate forwardDiff (2 ^ t) a) m =
            Nat.iterate forwardDiff (2 ^ t) a (m + 2 ^ t) + Nat.iterate forwardDiff (2 ^ t) a m :=
        by
          simpa [iteratedEPlusOneMod2] using
            (iteratedEPlusOneMod2_pow_two t (Nat.iterate forwardDiff (2 ^ t) a) m)
      rw [hfirst]
      have hleft :
          Nat.iterate forwardDiff (2 ^ t) a (m + 2 ^ t) =
            a ((m + 2 ^ t) + 2 ^ t) + a (m + 2 ^ t) := by
        simpa [iteratedEPlusOneMod2] using (iteratedEPlusOneMod2_pow_two t a (m + 2 ^ t))
      have hright : Nat.iterate forwardDiff (2 ^ t) a m = a (m + 2 ^ t) + a m := by
        simpa [iteratedEPlusOneMod2] using (iteratedEPlusOneMod2_pow_two t a m)
      rw [hleft, hright]
      rw [show m + (2 ^ t + 2 ^ t) = m + 2 ^ t + 2 ^ t by omega]
      ring_nf
      have htwo : (2 : ZMod 2) = 0 := by native_decide
      rw [htwo]
      simp

/-- If `(E + 1)^e` annihilates a mod-`2` sequence and `e ≤ 2^t`, then the tail is
`2^t`-periodic.
    cor:conclusion-mod2-eplus1-power-period -/
theorem paper_conclusion_mod2_eplus1_power_period (a : Nat -> ZMod 2) (e t : Nat) (he : 1 <= e)
    (ht : e <= 2 ^ t)
    (hann : forall sufficiently_large m : Nat, iteratedEPlusOneMod2 e a m = 0) :
    exists N : Nat, forall m : Nat, m >= N -> a (m + 2 ^ t) = a m := by
  let _ := he
  have hezero : iteratedEPlusOneMod2 e a = fun _ => 0 := by
    funext m
    exact hann 0 m
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le ht
  have hpowzero : iteratedEPlusOneMod2 (2 ^ t) a = fun _ => 0 := by
    rw [hr, iteratedEPlusOneMod2, Function.iterate_add_apply]
    have hcomm :
        Nat.iterate forwardDiff e (Nat.iterate forwardDiff r a) =
          Nat.iterate forwardDiff r (Nat.iterate forwardDiff e a) := by
      simpa using (Function.Commute.iterate_iterate_self forwardDiff e r).eq a
    rw [hcomm]
    have hiter := congrArg (Nat.iterate forwardDiff r) hezero
    simpa [iteratedEPlusOneMod2, iterate_forwardDiff_zero r] using hiter
  refine ⟨0, ?_⟩
  intro m hm
  let _ := hm
  have hsum : a (m + 2 ^ t) + a m = 0 := by
    simpa [iteratedEPlusOneMod2_pow_two] using congrFun hpowzero m
  have hself : a m + a m = 0 := by
    have htwo : (2 : ZMod 2) = 0 := by native_decide
    calc
      a m + a m = (2 : ZMod 2) * a m := by rw [two_mul]
      _ = 0 * a m := by rw [htwo]
      _ = 0 := by simp
  calc
    a (m + 2 ^ t) = a (m + 2 ^ t) + 0 := by simp
    _ = a (m + 2 ^ t) + (a m + a m) := by rw [hself]
    _ = (a (m + 2 ^ t) + a m) + a m := by abel_nf
    _ = 0 + a m := by rw [hsum]
    _ = a m := by simp

end Omega.Conclusion
