import Mathlib.Tactic

namespace Omega.POM

/-- The audited recurrence-order data used in the moment-dimension collapse package. -/
def auditedMomentOrders : List (ℕ × ℕ) :=
  [(9, 8), (10, 9), (11, 10), (12, 10), (13, 12), (14, 12), (15, 13), (16, 14),
   (17, 15), (18, 15), (19, 16), (20, 17), (21, 18), (22, 18), (23, 19)]

/-- The finite audited range `q = 9, …, 23`. -/
def auditedMomentRange : Finset ℕ :=
  Finset.Icc 9 23

/-- The recurrence order recorded for each audited `q`. Outside the audited window we return `0`. -/
def auditedMomentOrder : ℕ → ℕ
  | 9 => 8
  | 10 => 9
  | 11 => 10
  | 12 => 10
  | 13 => 12
  | 14 => 12
  | 15 => 13
  | 16 => 14
  | 17 => 15
  | 18 => 15
  | 19 => 16
  | 20 => 17
  | 21 => 18
  | 22 => 18
  | 23 => 19
  | _ => 0

/-- The naive closure-law dimension bound `2 * floor(q / 2) + 1`. -/
def naiveClosureDimension (q : ℕ) : ℕ :=
  2 * (q / 2) + 1

/-- Paper-facing moment-dimension collapse package: the audited orders for `q = 9, …, 23` are
recorded explicitly, every one of them lies strictly below the naive closure-law bound, and the
table therefore furnishes a counterexample family to that naive law.
    cor:pom-moment-dim-collapse -/
theorem paper_pom_moment_dim_collapse :
    (∀ q ∈ auditedMomentRange, auditedMomentOrder q < naiveClosureDimension q) ∧
    auditedMomentOrders =
      [(9, 8), (10, 9), (11, 10), (12, 10), (13, 12), (14, 12), (15, 13), (16, 14),
       (17, 15), (18, 15), (19, 16), (20, 17), (21, 18), (22, 18), (23, 19)] ∧
    (∃ q ∈ auditedMomentRange, auditedMomentOrder q ≠ naiveClosureDimension q) := by
  native_decide

end Omega.POM
