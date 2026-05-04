import Mathlib.Tactic

namespace Omega.Conclusion

/-- Audited mod-2 terminal-period bound for the resonance window `q = 9, ..., 17`. -/
def conclusion_resonance_window_dyadic_chambers_period_bound (q : ℕ) : ℕ :=
  if q ≤ 10 then 4 else if q ≤ 16 then 8 else 16

/-- Dyadic chamber level attached to the audited resonance window. -/
def conclusion_resonance_window_dyadic_chambers_level (q : ℕ) : ℕ :=
  if q ≤ 10 then 2 else if q ≤ 16 then 3 else 4

/-- The three concrete dyadic chamber assertions for the audited window. -/
def conclusion_resonance_window_dyadic_chambers_statement : Prop :=
  (∀ q : ℕ, 9 ≤ q → q ≤ 17 →
    (q ∈ ({9, 10} : Finset ℕ) ∧
        conclusion_resonance_window_dyadic_chambers_period_bound q ∣ 2 ^ 2) ∨
      (q ∈ Finset.Icc 11 16 ∧
        conclusion_resonance_window_dyadic_chambers_period_bound q ∣ 2 ^ 3) ∨
      (q = 17 ∧
        conclusion_resonance_window_dyadic_chambers_period_bound q ∣ 2 ^ 4)) ∧
    ∀ q r : ℕ, 9 ≤ q → q ≤ 17 →
      conclusion_resonance_window_dyadic_chambers_level q = r →
        r = 2 ∨ r = 3 ∨ r = 4

/-- Paper label: `thm:conclusion-resonance-window-dyadic-chambers`. -/
theorem paper_conclusion_resonance_window_dyadic_chambers :
    conclusion_resonance_window_dyadic_chambers_statement := by
  constructor
  · intro q hq9 hq17
    interval_cases q <;>
      simp [conclusion_resonance_window_dyadic_chambers_period_bound]
  · intro q r hq9 hq17 hr
    interval_cases q <;>
      simp [conclusion_resonance_window_dyadic_chambers_level] at hr <;>
      omega

end Omega.Conclusion
