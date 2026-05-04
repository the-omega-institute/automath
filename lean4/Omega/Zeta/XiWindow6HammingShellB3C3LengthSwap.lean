import Mathlib.Tactic
import Omega.Zeta.XiWindow6B3C3WeylInvariantImageQuadratic

namespace Omega.Zeta

/-- Concrete token for the window-`6` `B3/C3` Hamming-shell length-swap corollary. -/
abbrev xi_window6_hamming_shell_b3c3_length_swap_data :=
  Unit

namespace xi_window6_hamming_shell_b3c3_length_swap_data

/-- The `B3` shell selected by squared root length. -/
def xi_window6_hamming_shell_b3c3_length_swap_b3Shell
    (_D : xi_window6_hamming_shell_b3c3_length_swap_data) (q : ℤ) :
    List Omega.GU.Weight :=
  Omega.DerivedConsequences.derived_window6_b3c3_rootcloud_isotropic_design_b3_roots.filter
    (fun r => decide (Omega.GU.weightNormSq r = q))

/-- The `C3` shell selected by squared root length. -/
def xi_window6_hamming_shell_b3c3_length_swap_c3Shell
    (_D : xi_window6_hamming_shell_b3c3_length_swap_data) (q : ℤ) :
    List Omega.GU.Weight :=
  Omega.DerivedConsequences.derived_window6_b3c3_rootcloud_isotropic_design_c3_roots.filter
    (fun r => decide (Omega.GU.weightNormSq r = q))

/-- Concrete statement: the short `B3` shell has the same length as the long axial `C3` shell,
and the common off-axis shell length is transported unchanged. -/
def xi_window6_hamming_shell_b3c3_length_swap_statement
    (D : xi_window6_hamming_shell_b3c3_length_swap_data) : Prop :=
  (D.xi_window6_hamming_shell_b3c3_length_swap_b3Shell 1).length =
      (D.xi_window6_hamming_shell_b3c3_length_swap_c3Shell 4).length ∧
    (D.xi_window6_hamming_shell_b3c3_length_swap_b3Shell 2).length =
      (D.xi_window6_hamming_shell_b3c3_length_swap_c3Shell 2).length ∧
      (D.xi_window6_hamming_shell_b3c3_length_swap_b3Shell 1).length = 6 ∧
        (D.xi_window6_hamming_shell_b3c3_length_swap_b3Shell 2).length = 12 ∧
          (D.xi_window6_hamming_shell_b3c3_length_swap_c3Shell 2).length = 12 ∧
            (D.xi_window6_hamming_shell_b3c3_length_swap_c3Shell 4).length = 6

end xi_window6_hamming_shell_b3c3_length_swap_data

open xi_window6_hamming_shell_b3c3_length_swap_data

/-- Paper label: `cor:xi-window6-hamming-shell-b3c3-length-swap`. -/
theorem paper_xi_window6_hamming_shell_b3c3_length_swap
    (D : xi_window6_hamming_shell_b3c3_length_swap_data) :
    D.xi_window6_hamming_shell_b3c3_length_swap_statement := by
  rcases paper_xi_window6_b3c3_weyl_invariant_image_quadratic with
    ⟨hB1, hB2, hC2, hC4⟩
  simp [xi_window6_hamming_shell_b3c3_length_swap_statement,
    xi_window6_hamming_shell_b3c3_length_swap_b3Shell,
    xi_window6_hamming_shell_b3c3_length_swap_c3Shell, hB1, hB2, hC2, hC4]

end Omega.Zeta
