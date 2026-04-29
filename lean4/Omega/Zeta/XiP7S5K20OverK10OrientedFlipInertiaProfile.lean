import Mathlib.Data.List.Sort
import Mathlib.Tactic

namespace Omega.Zeta

/-- Minimal concrete carrier for the finite `K₂₀/K₁₀` oriented-pair cover calculation. -/
structure xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_data where
  xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_witness : Unit := ()

/-- The seven conjugacy-class representatives in `S₅`, encoded by row number. -/
def xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_perm (c n : ℕ) : ℕ :=
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

/-- The induced action on unordered pairs, stored in increasing order. -/
def xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_unordered_pair_action
    (c : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  let a := xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_perm c p.1
  let b := xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_perm c p.2
  if a ≤ b then (a, b) else (b, a)

/-- The induced action on ordered pairs of distinct points. -/
def xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_ordered_pair_action
    (c : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_perm c p.1,
    xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_perm c p.2)

/-- Orbit length found by bounded finite enumeration. -/
def xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_orbit_length
    {α : Type} [DecidableEq α] (f : α → α) (fuel : ℕ) (x : α) : ℕ :=
  match (List.range (fuel + 1)).find? (fun k => 0 < k ∧ Nat.iterate f k x = x) with
  | some k => k
  | none => 0

/-- The finite orbit generated from one seed. -/
def xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_orbit
    {α : Type} (f : α → α) (fuel : ℕ) (x : α) : List α :=
  (List.range fuel).map fun k => Nat.iterate f k x

/-- Greedy orbit decomposition with the oriented-return flag for each unordered-pair orbit. -/
def xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_oriented_rows_aux
    (c : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × Bool)
  | [], _ => []
  | x :: xs, seen =>
      if x ∈ seen then
        xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_oriented_rows_aux c xs seen
      else
        let m :=
          xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_orbit_length
            (xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_unordered_pair_action c)
            10 x
        let y :=
          Nat.iterate
            (xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_ordered_pair_action c)
            m x
        (m, y = (x.2, x.1)) ::
          xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_oriented_rows_aux c xs
            (seen ++
              xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_orbit
                (xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_unordered_pair_action c)
                10 x)

/-- The ten unordered pairs of the five-point set. -/
def xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_unordered_pairs :
    List (ℕ × ℕ) :=
  ((List.range 5).product (List.range 5)).filter fun p => p.1 < p.2

/-- The twenty ordered pairs of distinct points. -/
def xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_ordered_pairs :
    List (ℕ × ℕ) :=
  ((List.range 5).product (List.range 5)).filter fun p => p.1 ≠ p.2

/-- One row of the finite oriented-return table: unordered orbit length and inertness flag. -/
def xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_oriented_rows
    (c : ℕ) : List (ℕ × Bool) :=
  xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_oriented_rows_aux c
    xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_unordered_pairs []

/-- Residue-degree profile of inert primes in `K₂₀/K₁₀`, sorted descending. -/
def xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_inert_profile
    (c : ℕ) : List ℕ :=
  ((xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_oriented_rows c).filterMap
    fun r => if r.2 then some r.1 else none).insertionSort (fun a b : ℕ => b ≤ a)

/-- Residue-degree profile of split primes in `K₂₀/K₁₀`, sorted descending. -/
def xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_split_profile
    (c : ℕ) : List ℕ :=
  ((xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_oriented_rows c).filterMap
    fun r => if r.2 then none else some r.1).insertionSort (fun a b : ℕ => b ≤ a)

/-- Computed split/inert profile for the seven cycle types. -/
def xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_computed_profiles :
    List (ℕ × List ℕ × List ℕ) :=
  (List.range 7).map fun c =>
    (c, xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_split_profile c,
      xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_inert_profile c)

/-- Displayed split/inert profile for the seven cycle types. -/
def xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_expected_profiles :
    List (ℕ × List ℕ × List ℕ) :=
  [(0, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], []),
    (1, [2, 2, 2, 1, 1, 1], [1]),
    (2, [2, 2, 2, 2], [1, 1]),
    (3, [3, 3, 3, 1], []),
    (4, [6, 3], [1]),
    (5, [4, 4], [2]),
    (6, [5, 5], [])]

/-- Computed oriented-return criterion before sorting into split and inert profiles. -/
def xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_computed_oriented_rows :
    List (ℕ × List (ℕ × Bool)) :=
  (List.range 7).map fun c =>
    (c, xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_oriented_rows c)

/-- Displayed oriented-return table before sorting into split and inert profiles. -/
def xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_expected_oriented_rows :
    List (ℕ × List (ℕ × Bool)) :=
  [(0, [(1, false), (1, false), (1, false), (1, false), (1, false), (1, false),
      (1, false), (1, false), (1, false), (1, false)]),
    (1, [(1, true), (2, false), (2, false), (2, false), (1, false), (1, false),
      (1, false)]),
    (2, [(1, true), (2, false), (2, false), (2, false), (1, true), (2, false)]),
    (3, [(3, false), (3, false), (3, false), (1, false)]),
    (4, [(3, false), (6, false), (1, true)]),
    (5, [(4, false), (2, true), (4, false)]),
    (6, [(5, false), (5, false)])]

namespace xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_data

/-- The ordered-pair model is a double cover of the unordered-pair model. -/
def extensionQuadratic (_D : xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_data) :
    Prop :=
  xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_ordered_pairs.length =
    2 * xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_unordered_pairs.length

/-- Returning with flipped orientation is exactly the inert case in the finite model. -/
def orientedFlipCriterion
    (_D : xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_data) : Prop :=
  xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_computed_oriented_rows =
    xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_expected_oriented_rows

/-- The inert residue-degree profile matches the displayed seven-row table. -/
def inertiaProfileMatchesTable
    (_D : xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_data) : Prop :=
  xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_computed_profiles =
    xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_expected_profiles

end xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_data

/-- Paper label: `thm:xi-p7-s5-k20-over-k10-oriented-flip-inertia-profile`. -/
theorem paper_xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile
    (D : xi_p7_s5_k20_over_k10_oriented_flip_inertia_profile_data) :
    D.extensionQuadratic ∧ D.orientedFlipCriterion ∧ D.inertiaProfileMatchesTable := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl

end Omega.Zeta
