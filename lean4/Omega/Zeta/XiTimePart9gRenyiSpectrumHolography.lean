import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete entropy-window data for the Rényi spectrum holography statement.  The values
`renyiRate alpha eps m` and `multiplicityRate eps m` are already normalized by `m`; the
window hypothesis says the entropy rate differs from the multiplicity rate plus `gamma` by
at most the window width. -/
structure xi_time_part9g_renyi_spectrum_holography_data where
  xi_time_part9g_renyi_spectrum_holography_gamma : ℝ
  xi_time_part9g_renyi_spectrum_holography_limitMultiplicity : ℝ
  xi_time_part9g_renyi_spectrum_holography_multiplicityRate : ℝ → ℕ → ℝ
  xi_time_part9g_renyi_spectrum_holography_renyiRate : ℝ → ℝ → ℕ → ℝ
  xi_time_part9g_renyi_spectrum_holography_multiplicity_limit :
    ∀ η : ℝ,
      0 < η →
        ∃ ε₀ : ℝ,
          0 < ε₀ ∧
            ∀ ε : ℝ,
              0 < ε →
                ε ≤ ε₀ →
                  ∃ M : ℕ,
                    ∀ m : ℕ,
                      M ≤ m →
                        |xi_time_part9g_renyi_spectrum_holography_multiplicityRate ε m -
                          xi_time_part9g_renyi_spectrum_holography_limitMultiplicity| ≤ η
  xi_time_part9g_renyi_spectrum_holography_entropy_window :
    ∀ α ε : ℝ,
      0 < α →
        0 < ε →
          ∀ m : ℕ,
            |xi_time_part9g_renyi_spectrum_holography_renyiRate α ε m -
              (xi_time_part9g_renyi_spectrum_holography_multiplicityRate ε m +
                xi_time_part9g_renyi_spectrum_holography_gamma)| ≤ ε

namespace xi_time_part9g_renyi_spectrum_holography_data

/-- Finite-scale squeeze supplied by the entropy window. -/
def xi_time_part9g_renyi_spectrum_holography_finiteSqueeze
    (D : xi_time_part9g_renyi_spectrum_holography_data) : Prop :=
  ∀ α ε : ℝ,
    0 < α →
      0 < ε →
        ∀ m : ℕ,
          |D.xi_time_part9g_renyi_spectrum_holography_renyiRate α ε m -
            (D.xi_time_part9g_renyi_spectrum_holography_multiplicityRate ε m +
              D.xi_time_part9g_renyi_spectrum_holography_gamma)| ≤ ε

/-- The normalized double-window limiting statement, written as an explicit
eventual-in-`m`, small-in-`epsilon` Cauchy bound. -/
def xi_time_part9g_renyi_spectrum_holography_normalizedLimit
    (D : xi_time_part9g_renyi_spectrum_holography_data) : Prop :=
  ∀ α η : ℝ,
    0 < α →
      0 < η →
        ∃ ε₀ : ℝ,
          0 < ε₀ ∧
            ∀ ε : ℝ,
              0 < ε →
                ε ≤ ε₀ →
                  ∃ M : ℕ,
                    ∀ m : ℕ,
                      M ≤ m →
                        |D.xi_time_part9g_renyi_spectrum_holography_renyiRate α ε m -
                          (D.xi_time_part9g_renyi_spectrum_holography_limitMultiplicity +
                            D.xi_time_part9g_renyi_spectrum_holography_gamma)| ≤ η

/-- Paper-facing concrete statement: the finite entropy window squeezes every Rényi order, and
after normalizing the window limit is independent of the Rényi order. -/
def xi_time_part9g_renyi_spectrum_holography_statement
    (D : xi_time_part9g_renyi_spectrum_holography_data) : Prop :=
  D.xi_time_part9g_renyi_spectrum_holography_finiteSqueeze ∧
    D.xi_time_part9g_renyi_spectrum_holography_normalizedLimit

end xi_time_part9g_renyi_spectrum_holography_data

open xi_time_part9g_renyi_spectrum_holography_data

/-- Paper label: `thm:xi-time-part9g-renyi-spectrum-holography`. -/
theorem paper_xi_time_part9g_renyi_spectrum_holography
    (D : xi_time_part9g_renyi_spectrum_holography_data) :
    xi_time_part9g_renyi_spectrum_holography_statement D := by
  refine ⟨D.xi_time_part9g_renyi_spectrum_holography_entropy_window, ?_⟩
  intro α η hα hη
  have hη_half_pos : 0 < η / 2 := by linarith
  rcases D.xi_time_part9g_renyi_spectrum_holography_multiplicity_limit
      (η / 2) hη_half_pos with
    ⟨εmult, hεmult_pos, hmult⟩
  refine ⟨min εmult (η / 2), ⟨lt_min hεmult_pos hη_half_pos, ?_⟩⟩
  intro ε hε_pos hε_le
  have hε_le_mult : ε ≤ εmult := le_trans hε_le (min_le_left εmult (η / 2))
  have hε_le_half : ε ≤ η / 2 := le_trans hε_le (min_le_right εmult (η / 2))
  rcases hmult ε hε_pos hε_le_mult with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  have hEntropy :=
    D.xi_time_part9g_renyi_spectrum_holography_entropy_window α ε hα hε_pos m
  have hMultiplicity := hM m hm
  calc
    |D.xi_time_part9g_renyi_spectrum_holography_renyiRate α ε m -
        (D.xi_time_part9g_renyi_spectrum_holography_limitMultiplicity +
          D.xi_time_part9g_renyi_spectrum_holography_gamma)| =
        |(D.xi_time_part9g_renyi_spectrum_holography_renyiRate α ε m -
            (D.xi_time_part9g_renyi_spectrum_holography_multiplicityRate ε m +
              D.xi_time_part9g_renyi_spectrum_holography_gamma)) +
          (D.xi_time_part9g_renyi_spectrum_holography_multiplicityRate ε m -
            D.xi_time_part9g_renyi_spectrum_holography_limitMultiplicity)| := by
          congr 1
          ring
    _ ≤
        |D.xi_time_part9g_renyi_spectrum_holography_renyiRate α ε m -
            (D.xi_time_part9g_renyi_spectrum_holography_multiplicityRate ε m +
              D.xi_time_part9g_renyi_spectrum_holography_gamma)| +
          |D.xi_time_part9g_renyi_spectrum_holography_multiplicityRate ε m -
            D.xi_time_part9g_renyi_spectrum_holography_limitMultiplicity| := by
          exact abs_add_le _ _
    _ ≤ ε + η / 2 := by
          exact add_le_add hEntropy hMultiplicity
    _ ≤ η / 2 + η / 2 := by
          exact add_le_add hε_le_half le_rfl
    _ = η := by ring

end Omega.Zeta
