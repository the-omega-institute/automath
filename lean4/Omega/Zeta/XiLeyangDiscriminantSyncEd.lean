import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-leyang-discriminant-sync-ed`. -/
theorem paper_xi_leyang_discriminant_sync_ed :
    ((411 : ℤ) ^ 2 * (165 : ℤ) ^ 2 - 4 * 256 * (165 : ℤ) ^ 3 -
        4 * (411 : ℤ) ^ 3 * 32 - 27 * (256 : ℤ) ^ 2 * (32 : ℤ) ^ 2 +
          18 * 256 * 411 * 165 * 32 =
      -((3 : ℤ) ^ 9 * (31 : ℤ) ^ 2 * 37)) := by
  norm_num

end Omega.Zeta
