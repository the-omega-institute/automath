import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-rank2-rigidity-fibonacci-fusion-law`.
The coefficient-comparison core of the rank-two Fibonacci fusion-law rigidity argument. -/
theorem paper_pom_rank2_rigidity_fibonacci_fusion_law (a b : Nat) (u : Nat → Nat)
    (h1 : u 1 = 0) (h2 : u 2 = 1)
    (hrec : ∀ n, 1 ≤ n → u (n + 2) = a * u n + b * u (n + 1))
    (hfib : ∀ n, 1 ≤ n → u n = Nat.fib (n - 1)) : a = 1 ∧ b = 1 := by
  have hu3 : u 3 = 1 := by
    have h := hfib 3 (by norm_num)
    simpa using h
  have hu4 : u 4 = 2 := by
    have h := hfib 4 (by norm_num)
    simpa using h
  have hrec1 := hrec 1 (by norm_num)
  have hb : b = 1 := by
    rw [h1, h2] at hrec1
    norm_num [hu3] at hrec1
    omega
  have hrec2 := hrec 2 (by norm_num)
  have ha : a = 1 := by
    rw [h2, hu3, hb] at hrec2
    norm_num [hu4] at hrec2
    omega
  exact ⟨ha, hb⟩

end Omega.POM
