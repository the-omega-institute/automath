import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The golden carry parameter `z_* = φ^{-2}` used in the two-series compression. -/
def real_input_40_carry_constant_zStar : ℝ :=
  (Real.goldenRatio : ℝ)⁻¹ ^ (2 : ℕ)

/-- First quadratic-factor sum in the compressed carry bookkeeping. -/
def real_input_40_carry_constant_quadraticFactorSumLeft : ℝ :=
  real_input_40_carry_constant_zStar ^ 2 + real_input_40_carry_constant_zStar

/-- Second quadratic-factor sum in the compressed carry bookkeeping. -/
def real_input_40_carry_constant_quadraticFactorSumRight : ℝ :=
  1 - real_input_40_carry_constant_zStar ^ 2

/-- The trivial factor rewritten through the golden carry parameter. -/
def real_input_40_carry_constant_trivialFactor : ℝ :=
  (1 - real_input_40_carry_constant_zStar) ^ (2 : ℕ)

/-- Carry constant obtained by summing the two compressed quadratic contributions. -/
def real_input_40_carry_constant_constant : ℝ :=
  real_input_40_carry_constant_quadraticFactorSumLeft +
    real_input_40_carry_constant_quadraticFactorSumRight

lemma real_input_40_carry_constant_zStar_eq_two_sub_phi :
    real_input_40_carry_constant_zStar = 2 - Real.goldenRatio := by
  unfold real_input_40_carry_constant_zStar
  rw [Real.inv_goldenRatio]
  calc
    (-Real.goldenConj) ^ (2 : ℕ) = Real.goldenConj ^ (2 : ℕ) := by ring_nf
    _ = Real.goldenConj + 1 := Real.goldenConj_sq
    _ = 2 - Real.goldenRatio := by linarith [Real.goldenRatio_add_goldenConj]

lemma real_input_40_carry_constant_trivialFactor_eq_zStar :
    real_input_40_carry_constant_trivialFactor = real_input_40_carry_constant_zStar := by
  unfold real_input_40_carry_constant_trivialFactor
  rw [real_input_40_carry_constant_zStar_eq_two_sub_phi]
  calc
    (1 - (2 - Real.goldenRatio)) ^ (2 : ℕ) = (Real.goldenRatio - 1) ^ (2 : ℕ) := by ring_nf
    _ = (-Real.goldenConj) ^ (2 : ℕ) := by
      congr 1
      linarith [Real.one_sub_goldenConj]
    _ = Real.goldenConj ^ (2 : ℕ) := by ring_nf
    _ = Real.goldenConj + 1 := Real.goldenConj_sq
    _ = 2 - Real.goldenRatio := by linarith [Real.goldenRatio_add_goldenConj]

lemma real_input_40_carry_constant_quadratic :
    real_input_40_carry_constant_zStar ^ 2 - 3 * real_input_40_carry_constant_zStar + 1 = 0 := by
  rw [real_input_40_carry_constant_zStar_eq_two_sub_phi]
  nlinarith [Real.goldenRatio_sq]

lemma real_input_40_carry_constant_two_series_compression :
    real_input_40_carry_constant_quadraticFactorSumLeft +
        real_input_40_carry_constant_quadraticFactorSumRight =
      1 + real_input_40_carry_constant_zStar := by
  unfold real_input_40_carry_constant_quadraticFactorSumLeft
    real_input_40_carry_constant_quadraticFactorSumRight
  ring

/-- Paper label: `thm:real-input-40-carry-constant`. The two quadratic-factor sums compress to the
single carry constant `1 + z_*`, while the trivial factor rewrites to `z_* = φ^{-2}` and `z_*`
itself satisfies the golden quadratic `z_*^2 - 3 z_* + 1 = 0`. -/
theorem paper_real_input_40_carry_constant :
    real_input_40_carry_constant_quadraticFactorSumLeft +
        real_input_40_carry_constant_quadraticFactorSumRight =
      1 + real_input_40_carry_constant_zStar ∧
    real_input_40_carry_constant_trivialFactor = real_input_40_carry_constant_zStar ∧
    real_input_40_carry_constant_zStar ^ 2 - 3 * real_input_40_carry_constant_zStar + 1 = 0 ∧
    real_input_40_carry_constant_constant = 3 - Real.goldenRatio := by
  refine ⟨real_input_40_carry_constant_two_series_compression,
    real_input_40_carry_constant_trivialFactor_eq_zStar,
    real_input_40_carry_constant_quadratic, ?_⟩
  unfold real_input_40_carry_constant_constant
  rw [real_input_40_carry_constant_two_series_compression,
    real_input_40_carry_constant_zStar_eq_two_sub_phi]
  ring

end

end Omega.SyncKernelWeighted
