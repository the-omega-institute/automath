import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Conclusion.F2BinomialBasisFromDeltaNilpotent
import Omega.Conclusion.FiniteFieldJordanExponentPeriodBound
import Omega.Conclusion.Mod2EPlusOnePowerPeriod

namespace Omega.Conclusion

open scoped BigOperators fwdDiff

/-- A mod-`2` tail annihilated by the `b`-fold forward difference collapses to a binomial basis on
that tail, and the same tail is eventually periodic with period dividing `2 ^ b`.
    thm:conclusion-resonance-window-mod2-binomial-collapse -/
theorem paper_conclusion_resonance_window_mod2_binomial_collapse
    (a b m0 : Nat) (S : Nat -> ZMod 2)
    (hnil : ∀ n ≥ m0, Nat.iterate forwardDiff b (fun m => S (m + a)) n = 0) :
    ∃ c : Fin b -> ZMod 2,
      (∀ n ≥ m0, S (n + a) = ∑ j : Fin b, c j * (Nat.choose (n - m0) j : ZMod 2)) ∧
      ∃ T : Nat, T ∣ 2 ^ b ∧ EventuallyPeriodic (fun n => S (n + a)) T := by
  let shift : Nat → ZMod 2 := fun n => S (n + a)
  obtain ⟨c, hcoeffs⟩ := paper_conclusion_f2_binomial_basis_from_delta_nilpotent shift b m0 hnil
  refine ⟨c, hcoeffs, ?_⟩
  by_cases hb : b = 0
  · refine ⟨1, ?_, ?_⟩
    · simp [hb]
    · refine ⟨m0, ?_⟩
      intro n hn
      have hzero₁ : shift n = 0 := by
        simpa [shift, hb] using hnil n hn
      have hzero₂ : shift (n + 1) = 0 := by
        simpa [shift, hb] using hnil (n + 1) (le_trans hn (Nat.le_add_right n 1))
      simpa [shift] using hzero₂.trans hzero₁.symm
  · have hbpos : 1 ≤ b := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb)
    let tail : Nat → ZMod 2 := fun n => shift (n + m0)
    have htail_zero : ∀ n, Nat.iterate forwardDiff b tail n = 0 := by
      intro n
      have hbase : Δ_[1]^[b] shift (n + m0) = 0 := by
        simpa [iterate_forwardDiff_eq, shift, add_comm] using
          hnil (n + m0) (Nat.le_add_left m0 n)
      simpa [tail, iterate_forwardDiff_eq, forwardDiff, add_assoc, add_comm, add_left_comm] using
        (fwdDiff_iter_comp_add (h := 1) (f := shift) (m := m0) (n := b) (y := n)).trans hbase
    have hperiod_tail := paper_conclusion_mod2_eplus1_power_period tail b b hbpos
      (Nat.le_of_lt b.lt_two_pow_self) (by
        intro N n
        let _ := N
        exact htail_zero n)
    rcases hperiod_tail with ⟨N, hN⟩
    refine ⟨2 ^ b, dvd_rfl, ?_⟩
    refine ⟨m0 + N, ?_⟩
    intro n hn
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hr : N ≤ r + N := Nat.le_add_left N r
    have htail := hN (r + N) hr
    simpa [shift, tail, add_assoc, add_left_comm, add_comm] using htail

end Omega.Conclusion
