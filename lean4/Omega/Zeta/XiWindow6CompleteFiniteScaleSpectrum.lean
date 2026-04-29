import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-window6-complete-finite-scale-spectrum-closed-form`. -/
theorem paper_xi_window6_complete_finite_scale_spectrum_closed_form :
    (let S : ℕ → ℤ := fun q => 8 * (2 : ℤ) ^ q + 4 * (3 : ℤ) ^ q + 9 * (4 : ℤ) ^ q
     (∀ q : ℕ, S (q + 3) = 9 * S (q + 2) - 26 * S (q + 1) + 24 * S q) ∧
        S 0 = 21 ∧ S 1 = 64 ∧ S 2 = 212) := by
  dsimp
  constructor
  · intro q
    have hrec (a : ℤ) (ha : a ^ 3 = 9 * a ^ 2 - 26 * a + 24) :
        a ^ (q + 3) = 9 * a ^ (q + 2) - 26 * a ^ (q + 1) + 24 * a ^ q := by
      rw [pow_add, pow_add, pow_add, ha]
      ring
    have h2 : (2 : ℤ) ^ (q + 3) =
        9 * (2 : ℤ) ^ (q + 2) - 26 * (2 : ℤ) ^ (q + 1) + 24 * (2 : ℤ) ^ q :=
      hrec 2 (by norm_num)
    have h3 : (3 : ℤ) ^ (q + 3) =
        9 * (3 : ℤ) ^ (q + 2) - 26 * (3 : ℤ) ^ (q + 1) + 24 * (3 : ℤ) ^ q :=
      hrec 3 (by norm_num)
    have h4 : (4 : ℤ) ^ (q + 3) =
        9 * (4 : ℤ) ^ (q + 2) - 26 * (4 : ℤ) ^ (q + 1) + 24 * (4 : ℤ) ^ q :=
      hrec 4 (by norm_num)
    rw [h2, h3, h4]
    ring
  · norm_num

end Omega.Zeta
