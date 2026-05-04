import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-terminal-zm-leyang-double-cover-pullback-factorization`. -/
theorem paper_xi_terminal_zm_leyang_double_cover_pullback_factorization (u : ℚ) :
    let g : ℚ → ℚ := fun v => 324 * v ^ 3 - 540 * v ^ 2 + 333 * v - 74
    let iota : ℚ := (25 : ℚ) / 21 - u
    let y : ℚ → ℚ := fun v => -(1091 / 256) + (675 / 64) * v - (567 / 64) * v ^ 2
    let PLY : ℚ → ℚ := fun z => 256 * z ^ 3 + 411 * z ^ 2 + 165 * z + 32
    y iota = y u ∧
      PLY (y u) = ((3 : ℚ) ^ 4 * 7 ^ 3 / 2 ^ 14) * g u * g iota ∧
      y u * (y u - 1) * PLY (y u) =
        ((3 : ℚ) ^ 5 * 7 ^ 3 / 2 ^ 30) *
          (2268 * u ^ 2 - 2700 * u + 1091) *
            (756 * u ^ 2 - 900 * u + 449) * g u * g iota := by
  norm_num
  constructor
  · ring
  constructor <;> ring

end Omega.Zeta
