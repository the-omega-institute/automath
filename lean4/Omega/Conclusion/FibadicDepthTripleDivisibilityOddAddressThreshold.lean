import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fibadic-depth-triple-divisibility-odd-address-threshold`. -/
theorem paper_conclusion_fibadic_depth_triple_divisibility_odd_address_threshold
    (d : ℕ) (hd : 3 ≤ d) : (Odd (Nat.fib d) ↔ ¬ 3 ∣ d) := by
  let _ := hd
  rw [← Nat.not_even_iff_odd]
  exact not_congr (by simpa [even_iff_two_dvd] using Omega.fib_even_iff_three_dvd d)

end Omega.Conclusion
