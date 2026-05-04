import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-tail-offsets-maxfiber-triple-closure`.
The even-resolution max-fiber closed form at `k = 6, 7, 8` gives the Fibonacci triple
`{21, 34, 55}`. -/
theorem paper_xi_tail_offsets_maxfiber_triple_closure
    (D : ℕ → ℕ) (hD : ∀ k, D (2 * k) = Nat.fib (k + 2)) :
    ({Nat.fib 8, Nat.fib 9, Nat.fib 10} : Finset ℕ) = {21, 34, 55} ∧
      D 12 = 21 ∧ D 14 = 34 ∧ D 16 = 55 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · native_decide
  · have h := hD 6
    norm_num at h
    exact h
  · have h := hD 7
    norm_num at h
    exact h
  · have h := hD 8
    norm_num at h
    exact h

end Omega.Zeta
