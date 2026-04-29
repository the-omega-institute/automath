import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fiber-canonical-rowmotion-order-law`. If each path component
of length `ell` has rowmotion period `ell + 2`, then the product order is the lcm fold of the
component periods, and each component period divides that total order. -/
theorem paper_conclusion_fiber_canonical_rowmotion_order_law (componentOrder : Nat -> Nat)
    (lengths : List Nat) (hcomponent : forall ell, componentOrder ell = ell + 2) :
    (lengths.map componentOrder).foldl Nat.lcm 1 =
        lengths.foldl (fun acc ell => Nat.lcm acc (ell + 2)) 1 ∧
      (forall ell,
        ell ∈ lengths -> ell + 2 ∣ lengths.foldl (fun acc ell => Nat.lcm acc (ell + 2)) 1) := by
  constructor
  · have fold_map_eq :
        forall (tail : List Nat) (acc : Nat),
          (tail.map componentOrder).foldl Nat.lcm acc =
            tail.foldl (fun acc ell => Nat.lcm acc (ell + 2)) acc := by
      intro tail
      induction tail with
      | nil =>
          intro acc
          simp
      | cons ell tail ih =>
          intro acc
          simp [hcomponent ell, ih]
    exact fold_map_eq lengths 1
  · let step := fun acc ell => Nat.lcm acc (ell + 2)
    have dvd_of_dvd_acc :
        forall (tail : List Nat) (acc d : Nat), d ∣ acc -> d ∣ tail.foldl step acc := by
      intro tail
      induction tail with
      | nil =>
          intro acc d hd
          simpa using hd
      | cons ell tail ih =>
          intro acc d hd
          exact ih (step acc ell) d (Nat.dvd_trans hd (Nat.dvd_lcm_left acc (ell + 2)))
    have member_period_dvd :
        forall (tail : List Nat) (acc ell : Nat), ell ∈ tail -> ell + 2 ∣ tail.foldl step acc := by
      intro tail
      induction tail with
      | nil =>
          intro acc ell hell
          cases hell
      | cons head tail ih =>
          intro acc ell hell
          simp only [List.mem_cons] at hell
          rcases hell with rfl | hell
          · exact dvd_of_dvd_acc tail (step acc ell) (ell + 2)
              (Nat.dvd_lcm_right acc (ell + 2))
          · exact ih (step acc head) ell hell
    intro ell hell
    exact member_period_dvd lengths 1 ell hell

end Omega.Conclusion
