import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9z-window6-fixed-sector-distinct-collision`. -/
theorem paper_xi_time_part9z_window6_fixed_sector_distinct_collision
    (d : Fin 21 → ℕ) (hM1 : (∑ w, d w) = 64)
    (hM2 : (∑ w, (d w) ^ 2) = 212) :
    (∑ w, d w * (d w - 1)) = 148 := by
  have hpoint : ∀ w : Fin 21, d w * (d w - 1) = (d w) ^ 2 - d w := by
    intro w
    let n := d w
    change n * (n - 1) = n ^ 2 - n
    cases n with
    | zero =>
      simp
    | succ n =>
      rw [pow_two]
      rw [show (n + 1) * (n + 1) = (n + 1) * n + (n + 1) by ring]
      exact (Nat.add_sub_cancel_right ((n + 1) * n) (n + 1)).symm
  have hsum :
      (∑ w : Fin 21, d w * (d w - 1)) =
        (∑ w : Fin 21, (d w) ^ 2) - (∑ w : Fin 21, d w) := by
    calc
      (∑ w : Fin 21, d w * (d w - 1)) =
          ∑ w : Fin 21, ((d w) ^ 2 - d w) := by
        exact Finset.sum_congr rfl fun w _ => hpoint w
      _ = (∑ w : Fin 21, (d w) ^ 2) - (∑ w : Fin 21, d w) := by
        simpa using
          (Finset.sum_tsub_distrib (s := (Finset.univ : Finset (Fin 21)))
            (f := fun w : Fin 21 => (d w) ^ 2) (g := fun w : Fin 21 => d w) (by
              intro w _
              change d w ≤ (d w) ^ 2
              cases d w with
              | zero =>
                  simp
              | succ n =>
                  rw [pow_two]
                  exact Nat.le_mul_of_pos_right (n + 1) (Nat.succ_pos n)))
  rw [hsum, hM1, hM2]

end Omega.Zeta
