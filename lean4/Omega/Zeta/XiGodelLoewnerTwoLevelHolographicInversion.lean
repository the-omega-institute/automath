import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.XiGodelLoewnerExteriorBoxLoewnerHolographicWeight

namespace Omega.Zeta

noncomputable section

/-- Concrete two-level Loewner log-volume data.  The two affine identities are the two
instantiations of the exterior-box log-volume formula after division by the corresponding
coordinate counts. -/
structure xi_godel_loewner_two_level_holographic_inversion_data where
  xi_godel_loewner_two_level_holographic_inversion_k : ℕ
  xi_godel_loewner_two_level_holographic_inversion_t1 : ℕ
  xi_godel_loewner_two_level_holographic_inversion_t2 : ℕ
  xi_godel_loewner_two_level_holographic_inversion_k_pos :
    0 < xi_godel_loewner_two_level_holographic_inversion_k
  xi_godel_loewner_two_level_holographic_inversion_t1_lt_t2 :
    xi_godel_loewner_two_level_holographic_inversion_t1 <
      xi_godel_loewner_two_level_holographic_inversion_t2
  xi_godel_loewner_two_level_holographic_inversion_N1 : ℝ
  xi_godel_loewner_two_level_holographic_inversion_N2 : ℝ
  xi_godel_loewner_two_level_holographic_inversion_N1_ne_zero :
    xi_godel_loewner_two_level_holographic_inversion_N1 ≠ 0
  xi_godel_loewner_two_level_holographic_inversion_N2_ne_zero :
    xi_godel_loewner_two_level_holographic_inversion_N2 ≠ 0
  xi_godel_loewner_two_level_holographic_inversion_logVolume1 : ℝ
  xi_godel_loewner_two_level_holographic_inversion_logVolume2 : ℝ
  xi_godel_loewner_two_level_holographic_inversion_logKappa1 : ℝ
  xi_godel_loewner_two_level_holographic_inversion_logKappa2 : ℝ
  xi_godel_loewner_two_level_holographic_inversion_boundaryLogSum : ℝ
  xi_godel_loewner_two_level_holographic_inversion_level1 :
    xi_godel_loewner_two_level_holographic_inversion_logVolume1 /
        xi_godel_loewner_two_level_holographic_inversion_N1 =
      xi_godel_loewner_two_level_holographic_inversion_logKappa1 /
          xi_godel_loewner_two_level_holographic_inversion_N1 +
        (1 / 2 : ℝ) * Real.log xi_godel_loewner_two_level_holographic_inversion_N1 +
          (xi_godel_loewner_two_level_holographic_inversion_t1 : ℝ) /
            (xi_godel_loewner_two_level_holographic_inversion_k : ℝ) *
              xi_godel_loewner_two_level_holographic_inversion_boundaryLogSum
  xi_godel_loewner_two_level_holographic_inversion_level2 :
    xi_godel_loewner_two_level_holographic_inversion_logVolume2 /
        xi_godel_loewner_two_level_holographic_inversion_N2 =
      xi_godel_loewner_two_level_holographic_inversion_logKappa2 /
          xi_godel_loewner_two_level_holographic_inversion_N2 +
        (1 / 2 : ℝ) * Real.log xi_godel_loewner_two_level_holographic_inversion_N2 +
          (xi_godel_loewner_two_level_holographic_inversion_t2 : ℝ) /
            (xi_godel_loewner_two_level_holographic_inversion_k : ℝ) *
              xi_godel_loewner_two_level_holographic_inversion_boundaryLogSum

/-- The bracketed two-volume readout after removing the unit-ball and universal Loewner factors. -/
def xi_godel_loewner_two_level_holographic_inversion_readout
    (D : xi_godel_loewner_two_level_holographic_inversion_data) : ℝ :=
  D.xi_godel_loewner_two_level_holographic_inversion_logVolume1 /
      D.xi_godel_loewner_two_level_holographic_inversion_N1 -
    D.xi_godel_loewner_two_level_holographic_inversion_logVolume2 /
      D.xi_godel_loewner_two_level_holographic_inversion_N2 -
    (D.xi_godel_loewner_two_level_holographic_inversion_logKappa1 /
        D.xi_godel_loewner_two_level_holographic_inversion_N1 -
      D.xi_godel_loewner_two_level_holographic_inversion_logKappa2 /
        D.xi_godel_loewner_two_level_holographic_inversion_N2) -
    ((1 / 2 : ℝ) *
      (Real.log D.xi_godel_loewner_two_level_holographic_inversion_N1 -
        Real.log D.xi_godel_loewner_two_level_holographic_inversion_N2))

/-- Paper-facing statement: the boundary logarithmic sum is recovered from two normalized
Loewner volumes by solving the resulting one-variable linear equation. -/
def xi_godel_loewner_two_level_holographic_inversion_statement
    (D : xi_godel_loewner_two_level_holographic_inversion_data) : Prop :=
  D.xi_godel_loewner_two_level_holographic_inversion_boundaryLogSum =
    (D.xi_godel_loewner_two_level_holographic_inversion_k : ℝ) /
      ((D.xi_godel_loewner_two_level_holographic_inversion_t1 : ℝ) -
        (D.xi_godel_loewner_two_level_holographic_inversion_t2 : ℝ)) *
        xi_godel_loewner_two_level_holographic_inversion_readout D

/-- Paper label: `cor:xi-godel-loewner-two-level-holographic-inversion`. -/
theorem paper_xi_godel_loewner_two_level_holographic_inversion
    (D : xi_godel_loewner_two_level_holographic_inversion_data) :
    xi_godel_loewner_two_level_holographic_inversion_statement D := by
  have hk_ne :
      (D.xi_godel_loewner_two_level_holographic_inversion_k : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt D.xi_godel_loewner_two_level_holographic_inversion_k_pos)
  have ht_ne :
      (D.xi_godel_loewner_two_level_holographic_inversion_t1 : ℝ) -
          (D.xi_godel_loewner_two_level_holographic_inversion_t2 : ℝ) ≠ 0 := by
    have ht :
        (D.xi_godel_loewner_two_level_holographic_inversion_t1 : ℝ) <
          D.xi_godel_loewner_two_level_holographic_inversion_t2 := by
      exact_mod_cast D.xi_godel_loewner_two_level_holographic_inversion_t1_lt_t2
    linarith
  rw [xi_godel_loewner_two_level_holographic_inversion_statement,
    xi_godel_loewner_two_level_holographic_inversion_readout]
  rw [D.xi_godel_loewner_two_level_holographic_inversion_level1,
    D.xi_godel_loewner_two_level_holographic_inversion_level2]
  field_simp [hk_ne, ht_ne]
  ring

end

end Omega.Zeta
