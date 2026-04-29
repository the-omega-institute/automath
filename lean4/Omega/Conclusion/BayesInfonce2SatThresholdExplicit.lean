import Mathlib.Tactic

namespace Omega.Conclusion

/-- Binary SAT ambient size `N = 2^n`. -/
def conclusion_bayes_infonce2_sat_threshold_explicit_N (n : ℕ) : ℕ :=
  2 ^ n

/-- Closed-form second collision count for the two fibers of sizes `s` and `N - s`. -/
def conclusion_bayes_infonce2_sat_threshold_explicit_c2 (n s : ℕ) : ℕ :=
  s ^ 2 + (conclusion_bayes_infonce2_sat_threshold_explicit_N n - s) ^ 2

/-- The SAT-side separation gap. -/
def conclusion_bayes_infonce2_sat_threshold_explicit_satGap (n s : ℕ) : ℕ :=
  conclusion_bayes_infonce2_sat_threshold_explicit_N n - s

/-- The counting-side separation gap. -/
def conclusion_bayes_infonce2_sat_threshold_explicit_countingGap (_n s : ℕ) : ℕ :=
  s

/-- Concrete paper claim: the two fiber sizes give the closed form and exhaust `N`. -/
def conclusion_bayes_infonce2_sat_threshold_explicit_claim (n s : ℕ) : Prop :=
  conclusion_bayes_infonce2_sat_threshold_explicit_c2 n s =
      s ^ 2 + (conclusion_bayes_infonce2_sat_threshold_explicit_N n - s) ^ 2 ∧
    conclusion_bayes_infonce2_sat_threshold_explicit_satGap n s +
        conclusion_bayes_infonce2_sat_threshold_explicit_countingGap n s =
      conclusion_bayes_infonce2_sat_threshold_explicit_N n ∧
    s ≤ conclusion_bayes_infonce2_sat_threshold_explicit_N n

/-- Paper label: `thm:conclusion-bayes-infonce2-sat-threshold-explicit`. -/
theorem paper_conclusion_bayes_infonce2_sat_threshold_explicit (n s : Nat)
    (hs : s <= 2 ^ n) : conclusion_bayes_infonce2_sat_threshold_explicit_claim n s := by
  refine ⟨rfl, ?_, hs⟩
  exact Nat.sub_add_cancel hs

end Omega.Conclusion
