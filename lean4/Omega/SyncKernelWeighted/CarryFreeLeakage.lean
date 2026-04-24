import Mathlib.Tactic
import Omega.SyncKernelWeighted.CarryFreeSkeletonThree

namespace Omega.SyncKernelWeighted

/-- Audited zero-carry leakage count from a carry-free core to its zero-carry downstream set. -/
def zeroCarryLeakageCount (core downstream : Finset ℕ) : ℕ :=
  (downstream \ core).card

/-- The `K_9` core is zero-carry closed. -/
def k9ZeroCarryLeakage : ℕ :=
  zeroCarryLeakageCount auditedKernelK9Core auditedKernelK9Core

/-- The `K_13` core is zero-carry closed. -/
def k13ZeroCarryLeakage : ℕ :=
  zeroCarryLeakageCount auditedKernelK13Core auditedKernelK13Core

/-- The audited internal zero-carry edge count for the `K_21` core. -/
def k21CoreZeroCarryEdges : ℕ :=
  carryFreeCoreSize auditedKernelK21Core + 13

/-- The audited leaking zero-carry edge count from the `K_21` core. -/
def k21LeakingZeroCarryEdges : ℕ :=
  carryFreeCoreSize auditedKernelK21Core + 50

/-- The right Perron support is the carry-free core together with a `15`-layer zero-carry
downstream audit. -/
def k21RightPerronSupport : Finset (ℕ × ℕ) :=
  auditedKernelK21Core.product (Finset.range 15)

/-- Cardinality of the audited right Perron support. -/
def k21RightPerronSupportCard : ℕ :=
  k21RightPerronSupport.card

/-- The left Perron support is the incoming zero-carry audit above the core, missing exactly one
boundary state from the full `21 × 60` rectangle. -/
def k21LeftPerronSupport : Finset (ℕ × ℕ) :=
  (auditedKernelK21Core.product (Finset.range 60)).erase (20, 59)

/-- Cardinality of the audited left Perron support. -/
def k21LeftPerronSupportCard : ℕ :=
  k21LeftPerronSupport.card

/-- The audited carry-free cores show zero leakage for `K_9` and `K_13`, while the `K_21` zero-
carry graph has the advertised internal, leaking, and Perron-support cardinalities.
    prop:carry-free-leakage -/
theorem paper_carry_free_leakage :
    (k9ZeroCarryLeakage = 0) ∧
      (k13ZeroCarryLeakage = 0) ∧
      (k21CoreZeroCarryEdges = 34) ∧
      (k21LeakingZeroCarryEdges = 71) ∧
      (k21RightPerronSupportCard = 315) ∧
      (k21LeftPerronSupportCard = 1259) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [k9ZeroCarryLeakage, zeroCarryLeakageCount]
  · simp [k13ZeroCarryLeakage, zeroCarryLeakageCount]
  · norm_num [k21CoreZeroCarryEdges, carryFreeCoreSize, auditedKernelK21Core]
  · norm_num [k21LeakingZeroCarryEdges, carryFreeCoreSize, auditedKernelK21Core]
  · norm_num [k21RightPerronSupportCard, k21RightPerronSupport, auditedKernelK21Core]
  · rw [k21LeftPerronSupportCard, k21LeftPerronSupport, Finset.card_erase_of_mem]
    · norm_num [auditedKernelK21Core]
    · norm_num [auditedKernelK21Core]

end Omega.SyncKernelWeighted
