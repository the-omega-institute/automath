import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data token for the normalized Lee--Yang `a`-line `j`-map package. -/
structure xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_data where
  xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_witness : Unit := ()

/-- The quadratic factor in the normalized Legendre-form `j`-map. -/
def xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_q (a : ℚ) : ℚ :=
  a ^ 2 - a + 1

/-- The cubic critical factor whose branch value is `1728`. -/
def xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_c1728 (a : ℚ) : ℚ :=
  8 * a ^ 3 + 15 * a ^ 2 - 66 * a + 35

/-- The quadratic critical factor whose branch values generate `Q(√89)`. -/
def xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_c89 (a : ℚ) : ℚ :=
  2 * a ^ 2 - 9 * a - 1

/-- The non-ramified cubic factor in the denominator of the normalized `j(a)` map. -/
def xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_poleCubic
    (a : ℚ) : ℚ :=
  16 * a ^ 3 - 13 * a ^ 2 - 78 * a + 43

/-- Numerator of the normalized rational `j(a)` map. -/
def xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jNumerator
    (a : ℚ) : ℚ :=
  -4096 * xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_q a ^ 3

/-- Denominator of the normalized rational `j(a)` map. -/
def xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jDenominator
    (a : ℚ) : ℚ :=
  (a - 1) ^ 2 * xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_poleCubic a

/-- Product-rule numerator for the formal derivative of the rational `j(a)` map. -/
def xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_derivativeNumerator
    (a : ℚ) : ℚ :=
  (-12288 * xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_q a ^ 2 *
      (2 * a - 1)) *
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jDenominator a -
    xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jNumerator a *
      (2 * (a - 1) *
          xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_poleCubic a +
        (a - 1) ^ 2 * (48 * a ^ 2 - 26 * a - 78))

/-- Fully factored derivative numerator. -/
def xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_derivativeFactor
    (a : ℚ) : ℚ :=
  -4096 * (a - 1) * xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_q a ^ 2 *
    xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_c89 a *
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_c1728 a

/-- The local index over the branch value `0`. -/
def xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_indexOverZero : ℕ :=
  3

/-- The local index over the branch value `1728`. -/
def xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_indexOver1728 : ℕ :=
  2

/-- The local index over the branch value `∞`. -/
def xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_indexOverInfinity :
    ℕ :=
  2

namespace xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_data

/-- Degree-six numerator and normalized denominator expansion of the rational `j`-map. -/
def degreeSix
    (_D : xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_data) : Prop :=
  (∀ a : ℚ,
    xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jNumerator a =
      -4096 * a ^ 6 + 12288 * a ^ 5 - 24576 * a ^ 4 + 28672 * a ^ 3 -
        24576 * a ^ 2 + 12288 * a - 4096) ∧
    ∀ a : ℚ,
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jDenominator a =
        16 * a ^ 5 - 45 * a ^ 4 - 36 * a ^ 3 + 186 * a ^ 2 - 164 * a + 43

/-- The product-rule derivative numerator factors into the expected branch factors. -/
def derivativeFactorization
    (_D : xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_data) : Prop :=
  ∀ a : ℚ,
    xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_derivativeNumerator a =
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_derivativeFactor a

/-- The normalized map has branch values `0`, `1728`, and `∞` at the displayed fibers. -/
def branchValues
    (_D : xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_data) : Prop :=
  (∀ a : ℚ,
    xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_q a = 0 →
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jNumerator a = 0) ∧
    (∀ a : ℚ,
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_c1728 a = 0 →
        xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jNumerator a =
          1728 *
            xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jDenominator a) ∧
      (∀ a : ℚ,
        xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_c89 a = 0 →
          xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jNumerator a ^ 2 +
              1862 *
                xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jNumerator a *
                  xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jDenominator a +
                161792 *
                  xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jDenominator a ^
                    2 =
            0) ∧
        xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jDenominator 1 = 0

/-- Local ramification indices and the Riemann--Hurwitz contribution ledger. -/
def ramificationIndices
    (_D : xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_data) : Prop :=
  xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_indexOverZero = 3 ∧
    xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_indexOver1728 = 2 ∧
    xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_indexOverInfinity = 2 ∧
    2 *
        (xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_indexOverZero - 1) +
        3 *
          (xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_indexOver1728 -
            1) +
          2 *
            (xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_indexOverInfinity -
              1) +
            (xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_indexOverInfinity -
              1) =
      10

end xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_data

/-- Paper label:
`thm:xi-terminal-zm-leyang-spectral-quartic-a-j-ramification-spectrum`. -/
theorem paper_xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum
    (D : xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_data) :
    D.degreeSix ∧ D.derivativeFactorization ∧ D.branchValues ∧ D.ramificationIndices := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor <;> intro a <;>
      simp [xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jNumerator,
        xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jDenominator,
        xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_q,
        xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_poleCubic] <;> ring
  · intro a
    simp [xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_derivativeNumerator,
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_derivativeFactor,
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jNumerator,
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jDenominator,
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_q,
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_c1728,
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_c89,
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_poleCubic]
    ring
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro a ha
      simp [xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jNumerator, ha]
    · intro a ha
      have hdiff :
          xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jNumerator a -
              1728 *
                xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jDenominator a =
            -64 *
              xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_c1728 a ^ 2 := by
        simp [xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jNumerator,
          xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jDenominator,
          xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_q,
          xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_c1728,
          xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_poleCubic]
        ring
      rw [ha] at hdiff
      nlinarith
    · intro a ha
      have hquad :
          xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jNumerator a ^ 2 +
                1862 *
                  xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jNumerator a *
                    xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jDenominator a +
                  161792 *
                    xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jDenominator a ^
                      2 =
              2048 *
                xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_c89 a ^ 2 *
                  (2048 * a ^ 8 - 8752 * a ^ 7 + 16455 * a ^ 6 - 5030 * a ^ 5 -
                    39667 * a ^ 4 + 82096 * a ^ 3 - 74559 * a ^ 2 + 33406 * a -
                      5869) := by
        simp [xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jNumerator,
          xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jDenominator,
          xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_q,
          xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_c89,
          xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_poleCubic]
        ring
      rw [hquad, ha]
      ring
    · norm_num [xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_jDenominator,
        xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_poleCubic]
  · norm_num [
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_data.ramificationIndices,
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_indexOverZero,
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_indexOver1728,
      xi_terminal_zm_leyang_spectral_quartic_a_j_ramification_spectrum_indexOverInfinity]

end Omega.Zeta
