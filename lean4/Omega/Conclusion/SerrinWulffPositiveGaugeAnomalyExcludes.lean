import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-serrin-wulff-positive-gauge-anomaly-excludes`. Terminal
objects have zero gauge anomaly, and any positive anomaly contradicts intrinsic Serrin origin. -/
theorem paper_conclusion_serrin_wulff_positive_gauge_anomaly_excludes {Word : Type}
    (G : ℕ → Word → ℝ) (terminal : ℕ → Word) (intrinsic : ℕ → Word → Prop)
    (hterminal_zero : ∀ m, 1 ≤ m → G m (terminal (m + 1)) = 0)
    (hintrinsic_zero : ∀ m ω, 1 ≤ m → intrinsic m ω → G m ω = 0) :
    (∀ m, 1 ≤ m → G m (terminal (m + 1)) = 0) ∧
      ∀ m ω, 1 ≤ m → 0 < G m ω → ¬ intrinsic m ω := by
  constructor
  · exact hterminal_zero
  · intro m ω hm hpos hintrinsic
    have hzero : G m ω = 0 := hintrinsic_zero m ω hm hintrinsic
    linarith

end Omega.Conclusion
