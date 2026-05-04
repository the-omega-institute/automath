import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-leyang-gt-discriminant-and-special-fiber-factorization`. -/
theorem paper_xi_leyang_gt_discriminant_and_special_fiber_factorization :
    (∀ t : ℤ,
      let a : ℤ := 64 * t - 128
      let b : ℤ := 96 * t - 219
      let c : ℤ := 48 * t - 69
      let d : ℤ := 8 * t - 16
      b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 +
          18 * a * b * c * d =
        -(3 : ℤ) ^ 9 * (2304 * t ^ 2 - 8896 * t + 8549)) := by
  intro t
  ring_nf

end Omega.Zeta
