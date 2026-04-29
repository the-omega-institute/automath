import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Folding.ShiftDynamics

namespace Omega

/-- Paper label: `lem:pom-shifted-fib-fusion-defect-positive`. -/
theorem paper_pom_shifted_fib_fusion_defect_positive (a b : ℕ) :
    Nat.fib (a + 2) * Nat.fib (b + 2) =
        Nat.fib (a + b + 2) + Nat.fib a * Nat.fib b ∧
      Nat.fib (a + b + 2) ≤ Nat.fib (a + 2) * Nat.fib (b + 2) := by
  have hadd :
      Nat.fib (a + b + 2) =
        Nat.fib a * Nat.fib (b + 1) + Nat.fib (a + 1) * Nat.fib (b + 2) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.fib_add a (b + 1)
  have hmain :
      Nat.fib (a + 2) * Nat.fib (b + 2) =
        Nat.fib (a + b + 2) + Nat.fib a * Nat.fib b := by
    rw [Nat.fib_add_two (n := a), Nat.fib_add_two (n := b), hadd]
    rw [Nat.fib_add_two (n := b)]
    ring_nf
  refine ⟨hmain, ?_⟩
  rw [hmain]
  exact Nat.le_add_right _ _

/-- Paper label: `prop:pom-fusion-defect-2cocycle-identity`. -/
theorem paper_pom_fusion_defect_2cocycle_identity (a b c : Nat) :
    Nat.fib a * Nat.fib b * Nat.fib (c + 2) + Nat.fib (a + b) * Nat.fib c =
        Nat.fib b * Nat.fib c * Nat.fib (a + 2) + Nat.fib (b + c) * Nat.fib a ∧
      Nat.fib b * Nat.fib c * Nat.fib (a + 2) + Nat.fib (b + c) * Nat.fib a =
        Nat.fib c * Nat.fib a * Nat.fib (b + 2) + Nat.fib (c + a) * Nat.fib b := by
  exact ⟨fib_fusion_defect_cocycle a b c, fib_fusion_defect_cocycle b c a⟩

end Omega
