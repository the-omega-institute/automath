import Mathlib.Tactic

namespace Omega.Zeta

/-- The signed corner-contact count for a Lissajous pair with frequencies `a` and `b`. -/
def xi_time_part60ae_lissajous_singular_ring_contact_count_corner_count
    (a b : ℕ) : ℕ :=
  2 * Nat.gcd a b

/-- The inclusion-exclusion total for the two signed coordinate contact families. -/
def xi_time_part60ae_lissajous_singular_ring_contact_count_total_count
    (a b : ℕ) : ℕ :=
  2 * a + 2 * b -
    xi_time_part60ae_lissajous_singular_ring_contact_count_corner_count a b

/-- Paper label: `prop:xi-time-part60ae-lissajous-singular-ring-contact-count`.

Finite arithmetic core of the singular-ring contact count: if the two signed coordinate contact
families have sizes `2a` and `2b`, and their corner overlap is the gcd congruence count
`2 * gcd a b`, then the union has the expected inclusion-exclusion cardinality. -/
theorem paper_xi_time_part60ae_lissajous_singular_ring_contact_count
    {α : Type*} [DecidableEq α] (a b : ℕ) (first second : Finset α)
    (hfirst : first.card = 2 * a)
    (hsecond : second.card = 2 * b)
    (hcorner :
      (first ∩ second).card =
        xi_time_part60ae_lissajous_singular_ring_contact_count_corner_count a b) :
    (first ∪ second).card =
      xi_time_part60ae_lissajous_singular_ring_contact_count_total_count a b := by
  have hIE := Finset.card_union_add_card_inter first second
  unfold xi_time_part60ae_lissajous_singular_ring_contact_count_total_count at ⊢
  unfold xi_time_part60ae_lissajous_singular_ring_contact_count_corner_count at hcorner ⊢
  rw [← hcorner, ← hfirst, ← hsecond]
  exact Nat.eq_sub_of_add_eq hIE

end Omega.Zeta
