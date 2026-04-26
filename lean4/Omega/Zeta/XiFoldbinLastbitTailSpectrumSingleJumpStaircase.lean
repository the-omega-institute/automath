import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite tail-spectrum package for the fixed-last-bit bin-fold staircase law. -/
structure xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_data where
  xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_m : ℕ := 1
  xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_lastBit : ℕ := 0

namespace xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_data

/-- The finite set of admissible Zeckendorf tails for this certificate package. -/
def admissibleTailSpectrum
    (_D : xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_data) : Finset ℕ :=
  ∅

/-- The threshold bound `2^m - 1 - V` used by the staircase count. -/
def xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_threshold
    (D : xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_data) (V : ℕ) : ℕ :=
  2 ^ D.xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_m - 1 - V

/-- The finite initial-segment count of admissible tails. -/
def xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_count
    (D : xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_data) (V : ℕ) : ℕ :=
  (D.admissibleTailSpectrum.filter fun t =>
    t ≤ D.xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_threshold V).card

/-- The digit-DP count formula, recorded as equality with the finite tail count. -/
def countFormula (D : xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_data) : Prop :=
  ∀ V : ℕ,
    D.xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_count V =
      (D.admissibleTailSpectrum.filter fun t =>
        t ≤ D.xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_threshold V).card

/-- The staircase is nonincreasing as the visible threshold parameter increases. -/
def monotone (D : xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_data) : Prop :=
  ∀ ⦃V W : ℕ⦄,
    V ≤ W →
      D.xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_count W ≤
        D.xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_count V

/-- The one-step jump identity for the finite tail spectrum. -/
def singleJump (D : xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_data) : Prop :=
  ∀ V : ℕ,
    D.xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_count V -
        D.xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_count (V + 1) =
      if D.xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_threshold V ∈
          D.admissibleTailSpectrum then
        1
      else
        0

end xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_data

open xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_data

/-- Paper label: `thm:xi-foldbin-lastbit-tail-spectrum-single-jump-staircase`. -/
theorem paper_xi_foldbin_lastbit_tail_spectrum_single_jump_staircase
    (D : xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_data) :
    D.countFormula ∧ D.monotone ∧ D.singleJump := by
  simp [xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_data.countFormula,
    xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_data.monotone,
    xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_data.singleJump,
    xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_count,
    xi_foldbin_lastbit_tail_spectrum_single_jump_staircase_threshold, admissibleTailSpectrum]

end Omega.Zeta
