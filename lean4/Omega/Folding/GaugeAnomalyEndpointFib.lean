import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- `F_7 = 13`.
    thm:fold-gauge-anomaly-endpoint-fibonacci-mod3 -/
theorem fib_seven : Nat.fib 7 = 13 := by decide

/-- `F_8 = 21`.
    thm:fold-gauge-anomaly-endpoint-fibonacci-mod3 -/
theorem fib_eight_fold : Nat.fib 8 = 21 := by decide

/-- Recurrence seed `F_9 = F_8 + F_7`.
    thm:fold-gauge-anomaly-endpoint-fibonacci-mod3 -/
theorem fib_nine_eq_fib_eight_add_fib_seven :
    Nat.fib 9 = Nat.fib 8 + Nat.fib 7 := by
  rw [show (9 : ℕ) = 7 + 2 from rfl, Nat.fib_add_two]
  ring

/-- Abstract endpoint-event Fibonacci closure: any `ℕ → ℕ` sequence seeded
    at `U 2 = 13`, `U 3 = 21` and satisfying the two-step recurrence
    `U (m + 4) = U (m + 3) + U (m + 2)` is shifted Fibonacci, i.e.
    `U (m + 2) = F_{m + 7}`.
    thm:fold-gauge-anomaly-endpoint-fibonacci-mod3 -/
theorem abstract_endpoint_fibonacci
    (U : ℕ → ℕ)
    (h2 : U 2 = 13) (h3 : U 3 = 21)
    (hrec : ∀ m : ℕ, U (m + 4) = U (m + 3) + U (m + 2)) :
    ∀ m : ℕ, U (m + 2) = Nat.fib (m + 7) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    match m with
    | 0 => rw [h2]; decide
    | 1 => rw [h3]; decide
    | k + 2 =>
      -- U (k + 2 + 2) = U (k + 4) = U (k + 3) + U (k + 2)
      have hU : U (k + 2 + 2) = U (k + 3) + U (k + 2) := hrec k
      have ih1 : U (k + 1 + 2) = Nat.fib (k + 1 + 7) :=
        ih (k + 1) (by omega)
      have ih2 : U (k + 2) = Nat.fib (k + 7) := ih k (by omega)
      -- Rewrite the target `U (k + 2 + 2) = Nat.fib (k + 2 + 7)`
      rw [hU]
      have h1 : U (k + 3) = Nat.fib (k + 1 + 7) := by
        have : (k + 1 + 2) = k + 3 := by omega
        rw [← this]; exact ih1
      rw [h1, ih2]
      -- Nat.fib (k + 2 + 7) = Nat.fib (k + 1 + 7) + Nat.fib (k + 7)
      have hfib : Nat.fib (k + 2 + 7) = Nat.fib (k + 1 + 7) + Nat.fib (k + 7) := by
        have h1 : k + 2 + 7 = (k + 7) + 2 := by omega
        have h2 : k + 1 + 7 = (k + 7) + 1 := by omega
        rw [h1, Nat.fib_add_two, h2]
        ring
      rw [hfib]

/-- Paper package: endpoint-event Fibonacci closure with concrete Fib seeds.
    thm:fold-gauge-anomaly-endpoint-fibonacci-mod3 -/
theorem paper_fold_gauge_anomaly_endpoint_fibonacci_mod3 :
    Nat.fib 7 = 13 ∧
    Nat.fib 8 = 21 ∧
    Nat.fib 9 = 34 ∧
    Nat.fib 10 = 55 ∧
    Nat.fib 11 = 89 ∧
    (Nat.fib 9 = Nat.fib 8 + Nat.fib 7) ∧
    (Nat.fib 10 = Nat.fib 9 + Nat.fib 8) ∧
    (∀ (U : ℕ → ℕ) (_ : U 2 = 13) (_ : U 3 = 21)
       (_ : ∀ m, U (m + 4) = U (m + 3) + U (m + 2)) (m : ℕ),
       U (m + 2) = Nat.fib (m + 7)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · rw [show (9 : ℕ) = 7 + 2 from rfl, Nat.fib_add_two]; ring
  · rw [show (10 : ℕ) = 8 + 2 from rfl, Nat.fib_add_two]; ring
  · intro U h2 h3 hrec m
    exact abstract_endpoint_fibonacci U h2 h3 hrec m

end Omega.Folding
