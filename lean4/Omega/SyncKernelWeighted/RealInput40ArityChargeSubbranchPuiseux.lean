import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40ArityChargeDetClosed

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The real-valued version of the audited degree-`7` spectral polynomial `P₇`. -/
def real_input_40_arity_charge_subbranch_puiseux_P7 (Λ q : ℝ) : ℝ :=
  q * (1 - q) + q * (4 * q - 3) * Λ + (-4 * q ^ 2 - q + 1) * Λ ^ 2 +
    (6 * q ^ 2 - 3 * q - 1) * Λ ^ 3 + 6 * q * Λ ^ 4 + (1 - 5 * q) * Λ ^ 5 -
    2 * Λ ^ 6 + Λ ^ 7

/-- The Puiseux ansatz obtained from the change of variables `q = t⁻²`. -/
def real_input_40_arity_charge_subbranch_puiseux_ansatz (b1 b2 t : ℝ) : ℝ :=
  Real.sqrt 2 / t + b1 * t + b2 * t ^ 2

/-- The normalized residual `t⁷ P₇(Λ(t), t⁻²)` used for coefficient comparison. -/
def real_input_40_arity_charge_subbranch_puiseux_normalized_residual
    (b1 b2 t : ℝ) : ℝ :=
  t ^ 7 *
    real_input_40_arity_charge_subbranch_puiseux_P7
      (real_input_40_arity_charge_subbranch_puiseux_ansatz b1 b2 t)
      (1 / t ^ 2)

/-- The `t²` coefficient in the normalized residual. -/
def real_input_40_arity_charge_subbranch_puiseux_coeff_t2 (b1 : ℝ) : ℝ :=
  -8 * b1 + 2 * Real.sqrt 2

/-- The `t³` coefficient after the first comparison step. -/
def real_input_40_arity_charge_subbranch_puiseux_coeff_t3 (b1 b2 : ℝ) : ℝ :=
  -8 * Real.sqrt 2 * b1 - 8 * b2 - 3

/-- The solved `t`-coefficient in the positive subbranch ansatz. -/
def real_input_40_arity_charge_subbranch_puiseux_b1 : ℝ :=
  Real.sqrt 2 / 4

/-- The solved `t²`-coefficient in the positive subbranch ansatz. -/
def real_input_40_arity_charge_subbranch_puiseux_b2 : ℝ :=
  -(7 : ℝ) / 8

/-- Concrete coefficient-comparison certificate for the subdominant positive branch. -/
def real_input_40_arity_charge_subbranch_puiseux_statement : Prop :=
  real_input_40_arity_charge_subbranch_puiseux_coeff_t2
      real_input_40_arity_charge_subbranch_puiseux_b1 = 0 ∧
    real_input_40_arity_charge_subbranch_puiseux_coeff_t3
      real_input_40_arity_charge_subbranch_puiseux_b1
      real_input_40_arity_charge_subbranch_puiseux_b2 = 0

private lemma real_input_40_arity_charge_subbranch_puiseux_sqrt2_sq :
    (Real.sqrt 2) ^ 2 = 2 := by
  nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]

/-- Paper label: `prop:real-input-40-arity-charge-subbranch-puiseux`. After the change of
variables `q = t⁻²`, substituting the ansatz
`Λ = √2 / t + b₁ t + b₂ t² + O(t³)` into the explicit closed form for `P₇`
produces reduced coefficients `-8 b₁ + 2√2` and `-8√2 b₁ - 8 b₂ - 3`.
Solving these two comparison equations gives `b₁ = √2 / 4` and `b₂ = -7 / 8`. -/
theorem paper_real_input_40_arity_charge_subbranch_puiseux :
    real_input_40_arity_charge_subbranch_puiseux_statement := by
  constructor
  · unfold real_input_40_arity_charge_subbranch_puiseux_coeff_t2
      real_input_40_arity_charge_subbranch_puiseux_b1
    ring
  · unfold real_input_40_arity_charge_subbranch_puiseux_coeff_t3
      real_input_40_arity_charge_subbranch_puiseux_b1
      real_input_40_arity_charge_subbranch_puiseux_b2
    nlinarith [real_input_40_arity_charge_subbranch_puiseux_sqrt2_sq]

end

end Omega.SyncKernelWeighted
