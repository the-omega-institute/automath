import Mathlib.Tactic

namespace Omega.Zeta

/-- The cardinal predicted for the unit-circle touch ring of the rational rose orbit. -/
def xi_rose_unit_circle_touch_ring_parity_bifurcation_touch_card (d n : Nat) : Nat :=
  2 * n / Nat.gcd (2 * n) d

/-- A finite type carrying the touch-ring cardinality. -/
abbrev xi_rose_unit_circle_touch_ring_parity_bifurcation_touch_ring (d n : Nat) :=
  Fin (xi_rose_unit_circle_touch_ring_parity_bifurcation_touch_card d n)

/-- The touch-ring cardinal is `2n / gcd(2n,d)`, with the expected odd/even parity bifurcation in
the coprime regime. -/
def xi_rose_unit_circle_touch_ring_parity_bifurcation_statement (d n : Nat) : Prop :=
  Fintype.card (xi_rose_unit_circle_touch_ring_parity_bifurcation_touch_ring d n) =
      2 * n / Nat.gcd (2 * n) d ∧
    (Odd d →
      Fintype.card (xi_rose_unit_circle_touch_ring_parity_bifurcation_touch_ring d n) = 2 * n) ∧
    (Even d →
      Fintype.card (xi_rose_unit_circle_touch_ring_parity_bifurcation_touch_ring d n) = n)

private lemma xi_rose_unit_circle_touch_ring_parity_bifurcation_gcd_reduce
    (d n : Nat) (hcop : Nat.Coprime d n) :
    Nat.gcd (2 * n) d = Nat.gcd 2 d := by
  rw [Nat.mul_comm 2 n, Nat.Coprime.gcd_mul_left_cancel 2 hcop.symm]

private lemma xi_rose_unit_circle_touch_ring_parity_bifurcation_gcd_two_of_odd
    {d : Nat} (hodd : Odd d) : Nat.gcd 2 d = 1 := by
  rcases hodd with ⟨k, rfl⟩
  norm_num

private lemma xi_rose_unit_circle_touch_ring_parity_bifurcation_gcd_two_of_even
    {d : Nat} (heven : Even d) : Nat.gcd 2 d = 2 := by
  rcases heven with ⟨k, rfl⟩
  rw [← two_mul k]
  exact Nat.gcd_eq_left_iff_dvd.mpr (dvd_mul_right 2 k)

/-- Paper label: `prop:xi-rose-unit-circle-touch-ring-parity-bifurcation`. In the coprime regime,
the touch-ring order is `2n / gcd(2n,d)`, which collapses to `2n` for odd `d` and to `n` for even
`d`. -/
theorem paper_xi_rose_unit_circle_touch_ring_parity_bifurcation
    (d n : Nat) (hcop : Nat.Coprime d n) (hnd : n < d) :
    xi_rose_unit_circle_touch_ring_parity_bifurcation_statement d n := by
  let _ := hnd
  refine ⟨by simp [xi_rose_unit_circle_touch_ring_parity_bifurcation_touch_ring,
    xi_rose_unit_circle_touch_ring_parity_bifurcation_touch_card], ?_, ?_⟩
  · intro hodd
    have hgcd : Nat.gcd (2 * n) d = 1 := by
      rw [xi_rose_unit_circle_touch_ring_parity_bifurcation_gcd_reduce d n hcop,
        xi_rose_unit_circle_touch_ring_parity_bifurcation_gcd_two_of_odd hodd]
    calc
      Fintype.card (xi_rose_unit_circle_touch_ring_parity_bifurcation_touch_ring d n)
          = 2 * n / Nat.gcd (2 * n) d := by
              simp [xi_rose_unit_circle_touch_ring_parity_bifurcation_touch_ring,
                xi_rose_unit_circle_touch_ring_parity_bifurcation_touch_card]
      _ = 2 * n / 1 := by rw [hgcd]
      _ = 2 * n := by simp
  · intro heven
    have hgcd : Nat.gcd (2 * n) d = 2 := by
      rw [xi_rose_unit_circle_touch_ring_parity_bifurcation_gcd_reduce d n hcop,
        xi_rose_unit_circle_touch_ring_parity_bifurcation_gcd_two_of_even heven]
    calc
      Fintype.card (xi_rose_unit_circle_touch_ring_parity_bifurcation_touch_ring d n)
          = 2 * n / Nat.gcd (2 * n) d := by
              simp [xi_rose_unit_circle_touch_ring_parity_bifurcation_touch_ring,
                xi_rose_unit_circle_touch_ring_parity_bifurcation_touch_card]
      _ = 2 * n / 2 := by rw [hgcd]
      _ = n := by simp

end Omega.Zeta
