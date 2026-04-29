import Mathlib.Data.List.Sort
import Mathlib.Tactic

namespace Omega.Zeta

/-- The seven conjugacy-class representatives in `S₅`, encoded by their row number. -/
def xi_p7_s5_k5_k10_k20_splitting_type_table_perm (c n : ℕ) : ℕ :=
  match c with
  | 0 => n
  | 1 =>
      if n = 0 then 1 else if n = 1 then 0 else n
  | 2 =>
      if n = 0 then 1 else if n = 1 then 0 else if n = 2 then 3 else if n = 3 then 2 else n
  | 3 =>
      if n = 0 then 1 else if n = 1 then 2 else if n = 2 then 0 else n
  | 4 =>
      if n = 0 then 1 else if n = 1 then 2 else if n = 2 then 0 else if n = 3 then 4
        else if n = 4 then 3 else n
  | 5 =>
      if n = 0 then 1 else if n = 1 then 2 else if n = 2 then 3 else if n = 3 then 0 else n
  | _ =>
      if n = 0 then 1 else if n = 1 then 2 else if n = 2 then 3 else if n = 3 then 4
        else if n = 4 then 0 else n

/-- The induced action on two-subsets of `{0,1,2,3,4}`, stored as ordered pairs. -/
def xi_p7_s5_k5_k10_k20_splitting_type_table_two_subset_action
    (c : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  let a := xi_p7_s5_k5_k10_k20_splitting_type_table_perm c p.1
  let b := xi_p7_s5_k5_k10_k20_splitting_type_table_perm c p.2
  if a ≤ b then (a, b) else (b, a)

/-- The induced action on ordered pairs of distinct points. -/
def xi_p7_s5_k5_k10_k20_splitting_type_table_ordered_pair_action
    (c : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (xi_p7_s5_k5_k10_k20_splitting_type_table_perm c p.1,
    xi_p7_s5_k5_k10_k20_splitting_type_table_perm c p.2)

/-- Orbit length found by bounded finite enumeration. -/
def xi_p7_s5_k5_k10_k20_splitting_type_table_orbit_length
    {α : Type} [DecidableEq α] (f : α → α) (fuel : ℕ) (x : α) : ℕ :=
  match (List.range (fuel + 1)).find? (fun k => 0 < k ∧ Nat.iterate f k x = x) with
  | some k => k
  | none => 0

/-- The finite orbit generated from one seed. -/
def xi_p7_s5_k5_k10_k20_splitting_type_table_orbit
    {α : Type} (f : α → α) (fuel : ℕ) (x : α) : List α :=
  (List.range fuel).map fun k => Nat.iterate f k x

/-- Greedy orbit decomposition over a finite object list. -/
def xi_p7_s5_k5_k10_k20_splitting_type_table_orbit_profile_aux
    {α : Type} [DecidableEq α] (f : α → α) (fuel : ℕ) :
    List α → List α → List ℕ
  | [], _ => []
  | x :: xs, seen =>
      if x ∈ seen then
        xi_p7_s5_k5_k10_k20_splitting_type_table_orbit_profile_aux f fuel xs seen
      else
        xi_p7_s5_k5_k10_k20_splitting_type_table_orbit_length f fuel x ::
          xi_p7_s5_k5_k10_k20_splitting_type_table_orbit_profile_aux f fuel xs
            (seen ++ xi_p7_s5_k5_k10_k20_splitting_type_table_orbit f fuel x)

/-- Descending orbit-length profile for a finite action. -/
def xi_p7_s5_k5_k10_k20_splitting_type_table_orbit_profile
    {α : Type} [DecidableEq α] (f : α → α) (fuel : ℕ) (xs : List α) : List ℕ :=
  (xi_p7_s5_k5_k10_k20_splitting_type_table_orbit_profile_aux f fuel xs []).insertionSort
    (fun a b : ℕ => b ≤ a)

/-- The five-point set. -/
def xi_p7_s5_k5_k10_k20_splitting_type_table_points : List ℕ :=
  List.range 5

/-- The ten two-subsets of the five-point set. -/
def xi_p7_s5_k5_k10_k20_splitting_type_table_two_subsets : List (ℕ × ℕ) :=
  ((List.range 5).product (List.range 5)).filter fun p => p.1 < p.2

/-- The twenty ordered pairs of distinct points. -/
def xi_p7_s5_k5_k10_k20_splitting_type_table_ordered_pairs : List (ℕ × ℕ) :=
  ((List.range 5).product (List.range 5)).filter fun p => p.1 ≠ p.2

/-- The class-size table for the seven conjugacy classes of `S₅`. -/
def xi_p7_s5_k5_k10_k20_splitting_type_table_class_size (c : ℕ) : ℕ :=
  match c with
  | 0 => 1
  | 1 => 10
  | 2 => 15
  | 3 => 20
  | 4 => 20
  | 5 => 30
  | _ => 24

/-- One computed splitting-table row: class index, class size, group order, and three profiles. -/
def xi_p7_s5_k5_k10_k20_splitting_type_table_computed_row
    (c : ℕ) : ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ :=
  (c, xi_p7_s5_k5_k10_k20_splitting_type_table_class_size c, 120,
    xi_p7_s5_k5_k10_k20_splitting_type_table_orbit_profile
      (xi_p7_s5_k5_k10_k20_splitting_type_table_perm c) 5
      xi_p7_s5_k5_k10_k20_splitting_type_table_points,
    xi_p7_s5_k5_k10_k20_splitting_type_table_orbit_profile
      (xi_p7_s5_k5_k10_k20_splitting_type_table_two_subset_action c) 10
      xi_p7_s5_k5_k10_k20_splitting_type_table_two_subsets,
    xi_p7_s5_k5_k10_k20_splitting_type_table_orbit_profile
      (xi_p7_s5_k5_k10_k20_splitting_type_table_ordered_pair_action c) 20
      xi_p7_s5_k5_k10_k20_splitting_type_table_ordered_pairs)

/-- The computed finite-enumeration table. -/
def xi_p7_s5_k5_k10_k20_splitting_type_table_computed :
    List (ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ) :=
  (List.range 7).map xi_p7_s5_k5_k10_k20_splitting_type_table_computed_row

/-- The displayed splitting-type and class-density table. -/
def xi_p7_s5_k5_k10_k20_splitting_type_table_expected :
    List (ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ) :=
  [(0, 1, 120, [1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
    (1, 10, 120, [2, 1, 1, 1], [2, 2, 2, 1, 1, 1, 1],
      [2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1]),
    (2, 15, 120, [2, 2, 1], [2, 2, 2, 2, 1, 1],
      [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
    (3, 20, 120, [3, 1, 1], [3, 3, 3, 1], [3, 3, 3, 3, 3, 3, 1, 1]),
    (4, 20, 120, [3, 2], [6, 3, 1], [6, 6, 3, 3, 2]),
    (5, 30, 120, [4, 1], [4, 4, 2], [4, 4, 4, 4, 4]),
    (6, 24, 120, [5], [5, 5], [5, 5, 5, 5])]

/-- Concrete statement for the finite `S₅` splitting-type table. -/
def xi_p7_s5_k5_k10_k20_splitting_type_table_statement : Prop :=
  xi_p7_s5_k5_k10_k20_splitting_type_table_computed =
    xi_p7_s5_k5_k10_k20_splitting_type_table_expected

/-- Paper label: `thm:xi-p7-s5-k5-k10-k20-splitting-type-table`. -/
theorem paper_xi_p7_s5_k5_k10_k20_splitting_type_table :
    xi_p7_s5_k5_k10_k20_splitting_type_table_statement := by
  unfold xi_p7_s5_k5_k10_k20_splitting_type_table_statement
  rfl

end Omega.Zeta
