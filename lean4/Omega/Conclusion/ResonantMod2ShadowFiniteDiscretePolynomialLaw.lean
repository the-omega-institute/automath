import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Finset.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Conclusion.Mod2EPlusOnePowerPeriod
import Omega.Conclusion.ResonanceWindowMod2BinomialCollapse

namespace Omega.Conclusion

open scoped BigOperators fwdDiff

/-- Audited shift exponents `a_q` for the resonance-window mod-`2` shadow on `q = 9, …, 17`. -/
def conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_audited_a : ℕ → ℕ
  | 9 => 3
  | 10 => 5
  | 11 => 3
  | 12 => 5
  | 13 => 3
  | 14 => 5
  | 15 => 3
  | 16 => 5
  | 17 => 3
  | _ => 0

/-- Audited nilpotence exponents `b_q` for the resonance-window mod-`2` shadow on `q = 9, …, 17`. -/
def conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_audited_b : ℕ → ℕ
  | 9 => 4
  | 10 => 4
  | 11 => 6
  | 12 => 6
  | 13 => 6
  | 14 => 8
  | 15 => 8
  | 16 => 8
  | 17 => 9
  | _ => 0

/-- Dyadic exponent `t_q` chosen so that `b_q ≤ 2 ^ t_q` and the paper's three period ranges are
exactly `4`, `8`, and `16`. -/
def conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_exponent
    (q : ℕ) : ℕ :=
  if q = 9 ∨ q = 10 then 2 else if q = 17 then 4 else 3

/-- The explicit dyadic period bound attached to `q`. -/
def conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_bound
    (q : ℕ) : ℕ :=
  2 ^ conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_exponent q

private lemma conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_cases
    {q : ℕ} (hq : q ∈ Finset.Icc 9 17) :
    q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 15 ∨ q = 16 ∨ q = 17 := by
  rw [Finset.mem_Icc] at hq
  omega

private lemma conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_b_pos
    {q : ℕ} (hq : q ∈ Finset.Icc 9 17) :
    1 ≤ conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_audited_b q := by
  rcases conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_cases hq with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_b_le_period_bound
    {q : ℕ} (hq : q ∈ Finset.Icc 9 17) :
    conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_audited_b q ≤
      conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_bound q := by
  rcases conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_cases hq with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_ranges
    {q : ℕ} (hq : q ∈ Finset.Icc 9 17) :
    ((q = 9 ∨ q = 10) →
        conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_bound q = 4) ∧
      (11 ≤ q ∧ q ≤ 16 →
        conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_bound q = 8) ∧
      (q = 17 →
        conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_bound q = 16) := by
  rcases conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_cases hq with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_bound,
      conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_exponent]

/-- Paper label: `thm:conclusion-resonant-mod2-shadow-finite-discrete-polynomial-law`. On the
audited resonance window `q = 9, …, 17`, any mod-`2` shadow killed by the `b_q`-fold forward
difference after the shift `a_q` is eventually a discrete polynomial of degree `< b_q`, and its
eventual period divides the explicit dyadic bound `4`, `8`, or `16` according to the tabulated
range of `q`. -/
theorem paper_conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law
    (q : ℕ) (hq : q ∈ Finset.Icc 9 17) (S_q : ℕ → ZMod 2)
    (hnil : ∀ n ≥ 0,
      Nat.iterate forwardDiff
          (conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_audited_b q)
          (fun m => S_q
            (m + conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_audited_a q)) n = 0) :
    ∃ c : Fin (conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_audited_b q) →
        ZMod 2,
      (∀ n ≥ 0,
        S_q (n + conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_audited_a q) =
          ∑ j : Fin (conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_audited_b q),
            c j * (Nat.choose n j : ZMod 2)) ∧
      ∃ T : Nat,
        T ∣ conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_bound q ∧
          EventuallyPeriodic
            (fun n =>
              S_q (n + conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_audited_a q))
            T ∧
          (((q = 9 ∨ q = 10) →
              conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_bound q = 4) ∧
            (11 ≤ q ∧ q ≤ 16 →
              conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_bound q = 8) ∧
            (q = 17 →
              conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_bound q = 16)) := by
  rcases paper_conclusion_resonance_window_mod2_binomial_collapse
      (conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_audited_a q)
      (conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_audited_b q)
      0 S_q hnil with ⟨c, hcoeffs, _T, _hT, _hper⟩
  have hperiod :=
    paper_conclusion_mod2_eplus1_power_period
      (fun n => S_q (n + conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_audited_a q))
      (conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_audited_b q)
      (conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_exponent q)
      (conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_b_pos hq)
      (by
        simpa [conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_bound] using
          conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_b_le_period_bound hq)
      (by
        intro N n
        let _ := N
        exact hnil n (Nat.zero_le n))
  rcases hperiod with ⟨N, hN⟩
  refine ⟨c, ?_, conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_bound q,
    dvd_rfl, ?_, conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_ranges hq⟩
  · intro n hn
    simpa using hcoeffs n hn
  · refine ⟨N, ?_⟩
    intro n hn
    simpa [conclusion_resonant_mod2_shadow_finite_discrete_polynomial_law_period_bound] using
      hN n hn

end Omega.Conclusion
