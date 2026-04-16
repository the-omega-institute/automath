import Mathlib.Tactic
import Omega.Folding.BinFold
import Omega.POM.PrimeAxisVs2dExternalization

namespace Omega.TypedAddressBiaxialCompletion

open Omega.POM.PrimeAxisVs2dExternalization

/-- Fixed-window oracle capacity specialized to the window-6 histogram `8/4/9`. -/
def window6AuditCapacity (B : Nat) : Nat :=
  8 * min 2 (2 ^ B) + 4 * min 3 (2 ^ B) + 9 * min 4 (2 ^ B)

/-- Perfect-replay budget: the ceiling binary logarithm of the maximal window-6 fiber size. -/
def window6ReplayBudget : Nat :=
  Nat.clog 2 (cBinFiberMax 6)

/-- Boundary budget: the dual boundary parity group has cardinality `2^3`. -/
def window6BoundaryBudget : Nat :=
  Nat.clog 2 ((2 : Nat) ^ 3)

/-- Anomaly budget: the abelianized gauge-sign census has one bit per nontrivial window-6 fiber. -/
def window6AnomalyBudget : Nat :=
  cBinFiberHist 6 2 + cBinFiberHist 6 3 + cBinFiberHist 6 4

/-- Strict multiplicative ledgers cannot be injected into any finite additive register family. -/
def window6InfiniteRegisterBudget : Prop :=
  ∀ k : Nat, ∀ Φ : FreeMonoid (Fin 2) →* Multiplicative (Fin k → Nat), ¬ Function.Injective Φ

/-- Paper wrapper: the window-6 histogram fixes the `0/1/2` capacity values, the replay,
boundary, and anomaly budgets, and the impossibility of compressing a strict multiplicative ledger
into finitely many additive registers forces the infinite-register threshold.
    prop:typed-address-biaxial-completion-window6-audit-budget-split -/
theorem paper_typed_address_biaxial_completion_window6_audit_budget_split :
    (∀ B : Nat,
      window6AuditCapacity B = 8 * min 2 (2 ^ B) + 4 * min 3 (2 ^ B) + 9 * min 4 (2 ^ B)) ∧
    window6AuditCapacity 0 = 21 ∧
    window6AuditCapacity 1 = 42 ∧
    window6AuditCapacity 2 = 64 ∧
    (∀ B : Nat, window6AuditCapacity B = 64 ↔ 2 ≤ B) ∧
    window6ReplayBudget = 2 ∧
    window6BoundaryBudget = 3 ∧
    window6AnomalyBudget = 21 ∧
    window6BoundaryBudget - window6ReplayBudget = 1 ∧
    window6AnomalyBudget - window6ReplayBudget = 19 ∧
    window6InfiniteRegisterBudget := by
  have hcap := conclusion_window6_capacity_bifurcation
  rcases hcap with ⟨h0, h1, hsat⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro B
    rfl
  · simp [window6AuditCapacity] at h0 ⊢
  · simp [window6AuditCapacity] at h1 ⊢
  · have h2 := hsat 2 (by decide : 2 ≤ 2)
    simp [window6AuditCapacity] at h2 ⊢
  · intro B
    constructor
    · intro hB
      by_contra hBlt
      have hlt : B < 2 := Nat.lt_of_not_ge hBlt
      interval_cases B <;> simp [window6AuditCapacity] at hB
    · intro hB
      simpa [window6AuditCapacity] using hsat B hB
  · rw [window6ReplayBudget, cBinFiberMax_six]
    native_decide
  · rw [window6BoundaryBudget]
    native_decide
  · rw [window6AnomalyBudget, cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4]
  · rw [window6BoundaryBudget, window6ReplayBudget, cBinFiberMax_six]
    native_decide
  · rw [window6AnomalyBudget, window6ReplayBudget, cBinFiberMax_six,
      cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4]
    native_decide
  · intro k Φ
    exact paper_pom_prime_axis_vs_2d_noncommutative_externalization_part1 Φ 0 1 (by decide)

end Omega.TypedAddressBiaxialCompletion
