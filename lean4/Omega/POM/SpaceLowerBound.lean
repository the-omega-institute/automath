import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-space-lower-bound`. -/
theorem paper_pom_space_lower_bound
    (m hiddenFiber : ℕ) (fib : ℕ → ℕ)
    (hpos : 0 < fib (m + 2))
    (hcapacity : 2 ^ m ≤ hiddenFiber * fib (m + 2)) :
    (2 ^ m + fib (m + 2) - 1) / fib (m + 2) ≤ hiddenFiber := by
  let b := fib (m + 2)
  have hb : 0 < b := hpos
  have hcap : 2 ^ m ≤ hiddenFiber * b := hcapacity
  have hnum_lt : 2 ^ m + b - 1 < (hiddenFiber + 1) * b := by
    calc
      2 ^ m + b - 1 ≤ hiddenFiber * b + b - 1 := Nat.sub_le_sub_right (Nat.add_le_add_right hcap b) 1
      _ < hiddenFiber * b + b := Nat.sub_lt (Nat.add_pos_right _ hb) Nat.one_pos
      _ = (hiddenFiber + 1) * b := by rw [Nat.add_mul, Nat.one_mul]
  have hdiv_lt : (2 ^ m + b - 1) / b < hiddenFiber + 1 := by
    exact (Nat.div_lt_iff_lt_mul hb).2 hnum_lt
  exact Nat.lt_succ_iff.mp hdiv_lt

end Omega.POM
