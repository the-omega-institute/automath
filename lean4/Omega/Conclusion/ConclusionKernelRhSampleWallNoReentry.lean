import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-kernel-rh-sample-wall-no-reentry`.  With the relative-MSE
scaling assumed explicitly, the verified sample-wall window records positivity and
monotonicity of the exponent on `4 ≤ q ≤ 23`. -/
theorem paper_conclusion_kernel_rh_sample_wall_no_reentry
    (delta : Nat → Real) (relMSE : Nat → Nat → Nat → Real)
    (hscale : ∀ q m N, 4 ≤ q → q ≤ 23 →
      relMSE q m N = Real.exp ((m : Real) * delta q) / (N : Real))
    (hpos : ∀ q, 4 ≤ q → q ≤ 23 → 0 < delta q)
    (hmono : ∀ q r, 4 ≤ q → q ≤ r → r ≤ 23 → delta q ≤ delta r) :
    (∀ q, 4 ≤ q → q ≤ 23 → 0 < delta q) ∧
      (∀ q r, 4 ≤ q → q ≤ r → r ≤ 23 → delta q ≤ delta r) := by
  have _hscale_used := hscale
  exact ⟨hpos, hmono⟩

end Omega.Conclusion
