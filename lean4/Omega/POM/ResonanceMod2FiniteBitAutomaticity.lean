import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Conclusion.F2BinomialBasisFromDeltaNilpotent
import Omega.POM.Mod2DifferenceBinomialBasis
import Omega.POM.Mod2ShadowEventualPeriodBound

namespace Omega.POM

open scoped fwdDiff

private lemma mod2_iterate_forwardDiff_pow_two :
    ∀ t (a : ℕ → ZMod 2) (m : ℕ),
      Nat.iterate Omega.Conclusion.forwardDiff (2 ^ t) a m = a (m + 2 ^ t) + a m
  | 0, a, m => by
      simp [Omega.Conclusion.forwardDiff, fwdDiff, sub_eq_add_neg]
  | t + 1, a, m => by
      have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by
        omega
      rw [hpow, Function.iterate_add_apply]
      have hfirst :
          Nat.iterate Omega.Conclusion.forwardDiff (2 ^ t)
              (Nat.iterate Omega.Conclusion.forwardDiff (2 ^ t) a) m =
            Nat.iterate Omega.Conclusion.forwardDiff (2 ^ t) a (m + 2 ^ t) +
              Nat.iterate Omega.Conclusion.forwardDiff (2 ^ t) a m := by
        simpa using
          mod2_iterate_forwardDiff_pow_two t
            (Nat.iterate Omega.Conclusion.forwardDiff (2 ^ t) a) m
      rw [hfirst]
      have hleft :
          Nat.iterate Omega.Conclusion.forwardDiff (2 ^ t) a (m + 2 ^ t) =
            a ((m + 2 ^ t) + 2 ^ t) + a (m + 2 ^ t) := by
        simpa using mod2_iterate_forwardDiff_pow_two t a (m + 2 ^ t)
      have hright :
          Nat.iterate Omega.Conclusion.forwardDiff (2 ^ t) a m = a (m + 2 ^ t) + a m := by
        simpa using mod2_iterate_forwardDiff_pow_two t a m
      rw [hleft, hright]
      rw [show m + (2 ^ t + 2 ^ t) = m + 2 ^ t + 2 ^ t by omega]
      ring_nf
      have htwo : (2 : ZMod 2) = 0 := by native_decide
      rw [htwo]
      simp

private theorem mod2_shadow_pure_periodic_after
    (D : Mod2DifferenceBinomialBasisData) (k_q : ℕ) (hk : D.b ≤ 2 ^ k_q) :
    Mod2ShadowPurePeriodicAfter D.a D.m₀ (2 ^ k_q) := by
  let tail : ℕ → ZMod 2 := fun n => D.a (D.m₀ + n)
  dsimp [Mod2ShadowPurePeriodicAfter]
  by_cases hb : D.b = 0
  · intro n
    have hzero₁ : tail n = 0 := by
      simpa [tail, hb] using D.diffKilled n
    have hzero₂ : tail (n + 2 ^ k_q) = 0 := by
      simpa [tail, hb] using D.diffKilled (n + 2 ^ k_q)
    exact hzero₂.trans hzero₁.symm
  · have htail_zero : Nat.iterate Omega.Conclusion.forwardDiff D.b tail = fun _ => 0 := by
      funext n
      simpa [Omega.Conclusion.iterate_forwardDiff_eq, tail] using D.diffKilled n
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hk
    have hpowzero : Nat.iterate Omega.Conclusion.forwardDiff (2 ^ k_q) tail = fun _ => 0 := by
      rw [hr, Function.iterate_add_apply]
      have hcomm :
          Nat.iterate Omega.Conclusion.forwardDiff D.b
              (Nat.iterate Omega.Conclusion.forwardDiff r tail) =
            Nat.iterate Omega.Conclusion.forwardDiff r
              (Nat.iterate Omega.Conclusion.forwardDiff D.b tail) := by
        simpa using
          (Function.Commute.iterate_iterate_self Omega.Conclusion.forwardDiff D.b r).eq tail
      rw [hcomm]
      have hiter := congrArg (Nat.iterate Omega.Conclusion.forwardDiff r) htail_zero
      simpa [Omega.Conclusion.iterate_forwardDiff_zero r] using hiter
    intro n
    have hsum : tail (n + 2 ^ k_q) + tail n = 0 := by
      simpa [mod2_iterate_forwardDiff_pow_two] using congrFun hpowzero n
    have hself : tail n + tail n = 0 := by
      have htwo : (2 : ZMod 2) = 0 := by native_decide
      calc
        tail n + tail n = (2 : ZMod 2) * tail n := by rw [two_mul]
        _ = 0 * tail n := by rw [htwo]
        _ = 0 := by simp
    calc
      tail (n + 2 ^ k_q) = tail (n + 2 ^ k_q) + 0 := by simp
      _ = tail (n + 2 ^ k_q) + (tail n + tail n) := by rw [hself]
      _ = (tail (n + 2 ^ k_q) + tail n) + tail n := by abel_nf
      _ = 0 + tail n := by rw [hsum]
      _ = tail n := by simp

/-- Paper-facing mod-`2` resonance wrapper: the tail binomial-basis package supplies the unique
coefficient family, and the same tail is purely periodic with period `2 ^ k_q` as soon as
`b ≤ 2 ^ k_q`.
    thm:pom-resonance-mod2-finite-bit-automaticity -/
theorem paper_pom_resonance_mod2_finite_bit_automaticity
    (D : Mod2DifferenceBinomialBasisData) (k_q : ℕ) (hk : D.b ≤ 2 ^ k_q) :
    (∃! c : ℕ → ZMod 2,
      (∀ j, D.b ≤ j → c j = 0) ∧
        (∀ n, D.a (D.m₀ + n) = modpBinomialBasisEval c (n + 1) n)) ∧
      Mod2ShadowPurePeriodicAfter D.a D.m₀ (2 ^ k_q) := by
  refine ⟨(paper_pom_mod2_difference_binomial_basis D).2, ?_⟩
  exact mod2_shadow_pure_periodic_after D k_q hk

end Omega.POM
