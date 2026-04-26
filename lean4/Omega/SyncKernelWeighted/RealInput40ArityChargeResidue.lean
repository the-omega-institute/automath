import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40ArityChargeDetClosed

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Real-valued lift of the audited degree-`7` Perron polynomial. -/
def real_input_40_arity_charge_residue_P7_real (Λ q : ℝ) : ℝ :=
  q * (1 - q) + q * (4 * q - 3) * Λ + (-4 * q ^ 2 - q + 1) * Λ ^ 2 +
    (6 * q ^ 2 - 3 * q - 1) * Λ ^ 3 + 6 * q * Λ ^ 4 + (1 - 5 * q) * Λ ^ 5 -
    2 * Λ ^ 6 + Λ ^ 7

/-- Derivative of the real lift with respect to `Λ`. -/
def real_input_40_arity_charge_residue_P7_deriv_real (Λ q : ℝ) : ℝ :=
  q * (4 * q - 3) + 2 * (-4 * q ^ 2 - q + 1) * Λ + 3 * (6 * q ^ 2 - 3 * q - 1) * Λ ^ 2 +
    24 * q * Λ ^ 3 + 5 * (1 - 5 * q) * Λ ^ 4 - 12 * Λ ^ 5 + 7 * Λ ^ 6

/-- The `q = 1` Perron root coming from the factor `Λ² - 3Λ + 1`. -/
def real_input_40_arity_charge_residue_q1_perron_root : ℝ :=
  (3 + Real.sqrt 5) / 2

/-- The simple-root residue formula specialized to `q = 1`. -/
def real_input_40_arity_charge_residue_q1_pole_residue : ℝ :=
  let Λ := real_input_40_arity_charge_residue_q1_perron_root
  Λ ^ 9 / ((Λ + 1) * (Λ ^ 2 - 1) * real_input_40_arity_charge_residue_P7_deriv_real Λ 1)

/-- Concrete residue certificate at the unweighted specialization `q = 1`. -/
def real_input_40_arity_charge_residue_statement : Prop :=
  let Λ := real_input_40_arity_charge_residue_q1_perron_root
  real_input_40_arity_charge_residue_P7_real Λ 1 = 0 ∧
    real_input_40_arity_charge_residue_P7_deriv_real Λ 1 = 145 + 65 * Real.sqrt 5 ∧
    real_input_40_arity_charge_residue_q1_pole_residue = (47 + 21 * Real.sqrt 5) / 100

private lemma real_input_40_arity_charge_residue_sqrt5_sq :
    (Real.sqrt 5) ^ 2 = 5 := by
  nlinarith [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by positivity)]

private lemma real_input_40_arity_charge_residue_sqrt5_pow3 :
    (Real.sqrt 5) ^ 3 = 5 * Real.sqrt 5 := by
  calc
    (Real.sqrt 5) ^ 3 = (Real.sqrt 5) ^ 2 * Real.sqrt 5 := by ring
    _ = 5 * Real.sqrt 5 := by rw [real_input_40_arity_charge_residue_sqrt5_sq]

private lemma real_input_40_arity_charge_residue_sqrt5_pow4 :
    (Real.sqrt 5) ^ 4 = 25 := by
  calc
    (Real.sqrt 5) ^ 4 = ((Real.sqrt 5) ^ 2) ^ 2 := by ring
    _ = 25 := by rw [real_input_40_arity_charge_residue_sqrt5_sq]; norm_num

private lemma real_input_40_arity_charge_residue_q1_factorization (Λ : ℝ) :
    real_input_40_arity_charge_residue_P7_real Λ 1 =
      Λ * (Λ - 1) * (Λ + 1) * (Λ ^ 2 - 3 * Λ + 1) * (Λ ^ 2 + Λ - 1) := by
  unfold real_input_40_arity_charge_residue_P7_real
  ring

private lemma real_input_40_arity_charge_residue_q1_perron_root_quadratic :
    real_input_40_arity_charge_residue_q1_perron_root ^ 2 -
      3 * real_input_40_arity_charge_residue_q1_perron_root + 1 = 0 := by
  dsimp [real_input_40_arity_charge_residue_q1_perron_root]
  field_simp
  nlinarith [real_input_40_arity_charge_residue_sqrt5_sq]

private lemma real_input_40_arity_charge_residue_q1_perron_root_pow2 :
    real_input_40_arity_charge_residue_q1_perron_root ^ 2 =
      3 * real_input_40_arity_charge_residue_q1_perron_root - 1 := by
  nlinarith [real_input_40_arity_charge_residue_q1_perron_root_quadratic]

private lemma real_input_40_arity_charge_residue_q1_perron_root_pow3 :
    real_input_40_arity_charge_residue_q1_perron_root ^ 3 =
      8 * real_input_40_arity_charge_residue_q1_perron_root - 3 := by
  calc
    real_input_40_arity_charge_residue_q1_perron_root ^ 3 =
        real_input_40_arity_charge_residue_q1_perron_root *
          real_input_40_arity_charge_residue_q1_perron_root ^ 2 := by ring
    _ = real_input_40_arity_charge_residue_q1_perron_root *
          (3 * real_input_40_arity_charge_residue_q1_perron_root - 1) := by
          rw [real_input_40_arity_charge_residue_q1_perron_root_pow2]
    _ = 8 * real_input_40_arity_charge_residue_q1_perron_root - 3 := by
          nlinarith [real_input_40_arity_charge_residue_q1_perron_root_pow2]

private lemma real_input_40_arity_charge_residue_q1_perron_root_pow4 :
    real_input_40_arity_charge_residue_q1_perron_root ^ 4 =
      21 * real_input_40_arity_charge_residue_q1_perron_root - 8 := by
  calc
    real_input_40_arity_charge_residue_q1_perron_root ^ 4 =
        real_input_40_arity_charge_residue_q1_perron_root *
          real_input_40_arity_charge_residue_q1_perron_root ^ 3 := by ring
    _ = real_input_40_arity_charge_residue_q1_perron_root *
          (8 * real_input_40_arity_charge_residue_q1_perron_root - 3) := by
          rw [real_input_40_arity_charge_residue_q1_perron_root_pow3]
    _ = 21 * real_input_40_arity_charge_residue_q1_perron_root - 8 := by
          nlinarith [real_input_40_arity_charge_residue_q1_perron_root_pow2]

private lemma real_input_40_arity_charge_residue_q1_perron_root_pow5 :
    real_input_40_arity_charge_residue_q1_perron_root ^ 5 =
      55 * real_input_40_arity_charge_residue_q1_perron_root - 21 := by
  calc
    real_input_40_arity_charge_residue_q1_perron_root ^ 5 =
        real_input_40_arity_charge_residue_q1_perron_root *
          real_input_40_arity_charge_residue_q1_perron_root ^ 4 := by ring
    _ = real_input_40_arity_charge_residue_q1_perron_root *
          (21 * real_input_40_arity_charge_residue_q1_perron_root - 8) := by
          rw [real_input_40_arity_charge_residue_q1_perron_root_pow4]
    _ = 55 * real_input_40_arity_charge_residue_q1_perron_root - 21 := by
          nlinarith [real_input_40_arity_charge_residue_q1_perron_root_pow2]

private lemma real_input_40_arity_charge_residue_q1_perron_root_pow6 :
    real_input_40_arity_charge_residue_q1_perron_root ^ 6 =
      144 * real_input_40_arity_charge_residue_q1_perron_root - 55 := by
  calc
    real_input_40_arity_charge_residue_q1_perron_root ^ 6 =
        real_input_40_arity_charge_residue_q1_perron_root *
          real_input_40_arity_charge_residue_q1_perron_root ^ 5 := by ring
    _ = real_input_40_arity_charge_residue_q1_perron_root *
          (55 * real_input_40_arity_charge_residue_q1_perron_root - 21) := by
          rw [real_input_40_arity_charge_residue_q1_perron_root_pow5]
    _ = 144 * real_input_40_arity_charge_residue_q1_perron_root - 55 := by
          nlinarith [real_input_40_arity_charge_residue_q1_perron_root_pow2]

private lemma real_input_40_arity_charge_residue_q1_perron_root_pow9 :
    real_input_40_arity_charge_residue_q1_perron_root ^ 9 =
      2889 + 1292 * Real.sqrt 5 := by
  have hpow7 :
      real_input_40_arity_charge_residue_q1_perron_root ^ 7 =
        377 * real_input_40_arity_charge_residue_q1_perron_root - 144 := by
    calc
      real_input_40_arity_charge_residue_q1_perron_root ^ 7 =
          real_input_40_arity_charge_residue_q1_perron_root *
            real_input_40_arity_charge_residue_q1_perron_root ^ 6 := by ring
      _ = real_input_40_arity_charge_residue_q1_perron_root *
            (144 * real_input_40_arity_charge_residue_q1_perron_root - 55) := by
            rw [real_input_40_arity_charge_residue_q1_perron_root_pow6]
      _ = 377 * real_input_40_arity_charge_residue_q1_perron_root - 144 := by
            nlinarith [real_input_40_arity_charge_residue_q1_perron_root_pow2]
  have hpow8 :
      real_input_40_arity_charge_residue_q1_perron_root ^ 8 =
        987 * real_input_40_arity_charge_residue_q1_perron_root - 377 := by
    calc
      real_input_40_arity_charge_residue_q1_perron_root ^ 8 =
          real_input_40_arity_charge_residue_q1_perron_root *
            real_input_40_arity_charge_residue_q1_perron_root ^ 7 := by ring
      _ = real_input_40_arity_charge_residue_q1_perron_root *
            (377 * real_input_40_arity_charge_residue_q1_perron_root - 144) := by rw [hpow7]
      _ = 987 * real_input_40_arity_charge_residue_q1_perron_root - 377 := by
            nlinarith [real_input_40_arity_charge_residue_q1_perron_root_pow2]
  calc
    real_input_40_arity_charge_residue_q1_perron_root ^ 9 =
        real_input_40_arity_charge_residue_q1_perron_root *
          real_input_40_arity_charge_residue_q1_perron_root ^ 8 := by ring
    _ = real_input_40_arity_charge_residue_q1_perron_root *
          (987 * real_input_40_arity_charge_residue_q1_perron_root - 377) := by rw [hpow8]
    _ = 2584 * real_input_40_arity_charge_residue_q1_perron_root - 987 := by
          nlinarith [real_input_40_arity_charge_residue_q1_perron_root_pow2]
    _ = 2889 + 1292 * Real.sqrt 5 := by
          dsimp [real_input_40_arity_charge_residue_q1_perron_root]
          ring

private lemma real_input_40_arity_charge_residue_q1_perron_root_add_one :
    real_input_40_arity_charge_residue_q1_perron_root + 1 = (5 + Real.sqrt 5) / 2 := by
  dsimp [real_input_40_arity_charge_residue_q1_perron_root]
  ring

private lemma real_input_40_arity_charge_residue_q1_perron_root_sq_sub_one :
    real_input_40_arity_charge_residue_q1_perron_root ^ 2 - 1 = (5 + 3 * Real.sqrt 5) / 2 := by
  rw [real_input_40_arity_charge_residue_q1_perron_root_pow2]
  dsimp [real_input_40_arity_charge_residue_q1_perron_root]
  ring

/-- Paper label: `prop:real-input-40-arity-charge-residue`. The `q = 1` specialization of the
audited degree-`7` Perron factor has simple Perron root `(3 + √5)/2`, its denominator derivative
is `145 + 65 √5`, and the resulting simple-pole residue collapses to `(47 + 21 √5)/100`. -/
theorem paper_real_input_40_arity_charge_residue : real_input_40_arity_charge_residue_statement := by
  dsimp [real_input_40_arity_charge_residue_statement]
  constructor
  · rw [real_input_40_arity_charge_residue_q1_factorization]
    simp [real_input_40_arity_charge_residue_q1_perron_root_quadratic]
  constructor
  · unfold real_input_40_arity_charge_residue_P7_deriv_real
    rw [real_input_40_arity_charge_residue_q1_perron_root_pow2,
      real_input_40_arity_charge_residue_q1_perron_root_pow3,
      real_input_40_arity_charge_residue_q1_perron_root_pow4,
      real_input_40_arity_charge_residue_q1_perron_root_pow5,
      real_input_40_arity_charge_residue_q1_perron_root_pow6]
    dsimp [real_input_40_arity_charge_residue_q1_perron_root]
    ring
  · unfold real_input_40_arity_charge_residue_q1_pole_residue
    dsimp
    rw [real_input_40_arity_charge_residue_q1_perron_root_pow9,
      real_input_40_arity_charge_residue_q1_perron_root_add_one,
      real_input_40_arity_charge_residue_q1_perron_root_sq_sub_one]
    have hderiv :
        real_input_40_arity_charge_residue_P7_deriv_real
            real_input_40_arity_charge_residue_q1_perron_root 1 =
          145 + 65 * Real.sqrt 5 := by
      unfold real_input_40_arity_charge_residue_P7_deriv_real
      rw [real_input_40_arity_charge_residue_q1_perron_root_pow2,
        real_input_40_arity_charge_residue_q1_perron_root_pow3,
        real_input_40_arity_charge_residue_q1_perron_root_pow4,
        real_input_40_arity_charge_residue_q1_perron_root_pow5,
        real_input_40_arity_charge_residue_q1_perron_root_pow6]
      dsimp [real_input_40_arity_charge_residue_q1_perron_root]
      ring
    rw [hderiv]
    have hden : ((5 + Real.sqrt 5) / 2) * ((5 + 3 * Real.sqrt 5) / 2) * (145 + 65 * Real.sqrt 5) ≠ 0 := by
      positivity
    field_simp [hden]
    ring_nf
    rw [real_input_40_arity_charge_residue_sqrt5_pow4,
      real_input_40_arity_charge_residue_sqrt5_pow3,
      real_input_40_arity_charge_residue_sqrt5_sq]
    nlinarith [real_input_40_arity_charge_residue_sqrt5_sq]

end

end Omega.SyncKernelWeighted
