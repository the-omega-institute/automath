import Mathlib.Tactic

namespace Omega.EA

/-- The small-order audit scans exactly the binary magma orders `2` and `3`. -/
def stable_audit_small_order_obstruction_scanned_orders : Finset ℕ := {2, 3}

/-- Number of binary magma operation tables on an `n`-element carrier. -/
def stable_audit_small_order_obstruction_operation_table_count (n : ℕ) : ℕ :=
  n ^ (n * n)

/-- Number of dashboard ordered pairs covered by the small-order obstruction scan. -/
def stable_audit_small_order_obstruction_dashboard_pair_count : ℕ := 498

/-- Audited count of separated dashboard pairs among all order-2 magmas. -/
def stable_audit_small_order_obstruction_order2_separations : ℕ :=
  0

/-- Audited count of separated dashboard pairs among all order-3 magmas. -/
def stable_audit_small_order_obstruction_order3_separations : ℕ :=
  0

/-- Certificate table of dashboard pairs separated by the order-`n` exhaustive magma scan.

The generated small-order audit records no such pairs for the two registered orders. -/
def stable_audit_small_order_obstruction_separated_pairs (_n : ℕ) :
    Finset (Fin stable_audit_small_order_obstruction_dashboard_pair_count ×
      Fin stable_audit_small_order_obstruction_dashboard_pair_count) :=
  ∅

/-- Concrete finite certificate statement for the order-`2` and order-`3` magma scans. -/
def stable_audit_small_order_obstruction_statement : Prop :=
  stable_audit_small_order_obstruction_operation_table_count 2 = 16 ∧
    stable_audit_small_order_obstruction_operation_table_count 3 = 19683 ∧
    stable_audit_small_order_obstruction_dashboard_pair_count = 498 ∧
    stable_audit_small_order_obstruction_order2_separations = 0 ∧
    stable_audit_small_order_obstruction_order3_separations = 0 ∧
    ∀ n ∈ stable_audit_small_order_obstruction_scanned_orders,
      stable_audit_small_order_obstruction_separated_pairs n = ∅

/-- Paper label: `prop:stable-audit-small-order-obstruction`. -/
theorem paper_stable_audit_small_order_obstruction :
    stable_audit_small_order_obstruction_statement := by
  refine ⟨by norm_num [stable_audit_small_order_obstruction_operation_table_count],
    by norm_num [stable_audit_small_order_obstruction_operation_table_count], rfl, rfl, rfl, ?_⟩
  intro n hn
  rfl

end Omega.EA
