import Mathlib.Tactic
import Omega.Zeta.XiWindow6C3QuadraticEnergyEquipartition

namespace Omega.Zeta

/-- Paper label: `thm:xi-window6-c3-hamming-root-length-split`. -/
theorem paper_xi_window6_c3_hamming_root_length_split :
    xiWindow6LongRoots = [((2 : ℤ), 0, 0), ((-2 : ℤ), 0, 0), (0, (2 : ℤ), 0), (0, (-2 : ℤ), 0),
      (0, 0, (2 : ℤ)), (0, 0, (-2 : ℤ))] ∧
      xiWindow6ShortRoots = [((1 : ℤ), (1 : ℤ), 0), ((1 : ℤ), (-1 : ℤ), 0),
        (((-1 : ℤ)), (1 : ℤ), 0), (((-1 : ℤ)), (-1 : ℤ), 0), ((1 : ℤ), 0, (1 : ℤ)),
        ((1 : ℤ), 0, (-1 : ℤ)), (((-1 : ℤ)), 0, (1 : ℤ)), (((-1 : ℤ)), 0, (-1 : ℤ)),
        (0, (1 : ℤ), (1 : ℤ)), (0, (1 : ℤ), (-1 : ℤ)), (0, (-1 : ℤ), (1 : ℤ)),
        (0, (-1 : ℤ), (-1 : ℤ))] := by
  simp [xiWindow6LongRoots, xiWindow6ShortRoots]

end Omega.Zeta
