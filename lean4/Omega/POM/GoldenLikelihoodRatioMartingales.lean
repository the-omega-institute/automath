import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- The golden-ratio Bernoulli mass of observing `1` under the `θ₊` phase. -/
noncomputable def pom_golden_likelihood_ratio_martingales_plusProb : ℝ :=
  Real.goldenRatio⁻¹

/-- The complementary golden-ratio Bernoulli mass of observing `1` under the `θ₋` phase. -/
noncomputable def pom_golden_likelihood_ratio_martingales_minusProb : ℝ :=
  pom_golden_likelihood_ratio_martingales_plusProb ^ 2

/-- The single-step signed increment `Y = 2 B - 1`. -/
def pom_golden_likelihood_ratio_martingales_stepIncrement : Bool → Int
  | true => 1
  | false => -1

/-- The one-step likelihood-ratio multiplier. -/
noncomputable def pom_golden_likelihood_ratio_martingales_stepRatio : Bool → ℝ
  | true => Real.goldenRatio
  | false => Real.goldenRatio⁻¹

/-- The log-likelihood exponent `K_n = Σ_i (2 B_i - 1)` on a finite path. -/
def pom_golden_likelihood_ratio_martingales_walkExponent : List Bool → Int
  | [] => 0
  | b :: bs =>
      pom_golden_likelihood_ratio_martingales_stepIncrement b +
        pom_golden_likelihood_ratio_martingales_walkExponent bs

/-- The finite-path likelihood ratio `L_n`. -/
noncomputable def pom_golden_likelihood_ratio_martingales_likelihoodRatio : List Bool → ℝ
  | [] => 1
  | b :: bs =>
      pom_golden_likelihood_ratio_martingales_stepRatio b *
        pom_golden_likelihood_ratio_martingales_likelihoodRatio bs

/-- One-step Bernoulli mass under `θ₋`. -/
noncomputable def pom_golden_likelihood_ratio_martingales_minusMass : Bool → ℝ
  | true => pom_golden_likelihood_ratio_martingales_minusProb
  | false => pom_golden_likelihood_ratio_martingales_plusProb

/-- One-step Bernoulli mass under `θ₊`. -/
noncomputable def pom_golden_likelihood_ratio_martingales_plusMass : Bool → ℝ
  | true => pom_golden_likelihood_ratio_martingales_plusProb
  | false => pom_golden_likelihood_ratio_martingales_minusProb

/-- Recursive `θ₋` expectation of `L_n`, using independence and the one-step conditional
expectation. -/
noncomputable def pom_golden_likelihood_ratio_martingales_minusExpectation : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      pom_golden_likelihood_ratio_martingales_minusExpectation n *
        (pom_golden_likelihood_ratio_martingales_minusMass true *
            pom_golden_likelihood_ratio_martingales_stepRatio true +
          pom_golden_likelihood_ratio_martingales_minusMass false *
            pom_golden_likelihood_ratio_martingales_stepRatio false)

/-- Recursive `θ₊` expectation of `L_n⁻¹`, again reduced to the one-step identity. -/
noncomputable def pom_golden_likelihood_ratio_martingales_plusDualExpectation : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      pom_golden_likelihood_ratio_martingales_plusDualExpectation n *
        (pom_golden_likelihood_ratio_martingales_plusMass true *
            (pom_golden_likelihood_ratio_martingales_stepRatio true)⁻¹ +
          pom_golden_likelihood_ratio_martingales_plusMass false *
            (pom_golden_likelihood_ratio_martingales_stepRatio false)⁻¹)

/-- A bounded stopping law on the time set `{0, …, N}`. -/
abbrev pom_golden_likelihood_ratio_martingales_stoppingLaw (N : ℕ) := Fin (N + 1) → ℝ

/-- The stopped `θ₋` expectation obtained by averaging the horizon expectations over a bounded
stopping law. -/
noncomputable def pom_golden_likelihood_ratio_martingales_stoppedMinusExpectation {N : ℕ}
    (ρ : pom_golden_likelihood_ratio_martingales_stoppingLaw N) : ℝ :=
  ∑ i, ρ i * pom_golden_likelihood_ratio_martingales_minusExpectation i.1

/-- The stopped `θ₊` expectation of the dual likelihood-ratio martingale. -/
noncomputable def pom_golden_likelihood_ratio_martingales_stoppedPlusDualExpectation {N : ℕ}
    (ρ : pom_golden_likelihood_ratio_martingales_stoppingLaw N) : ℝ :=
  ∑ i, ρ i * pom_golden_likelihood_ratio_martingales_plusDualExpectation i.1

lemma pom_golden_likelihood_ratio_martingales_inv_eq_sub_one :
    Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
  have hinvψ : Real.goldenRatio⁻¹ = -Real.goldenConj := by
    simpa [one_div] using Real.inv_goldenRatio
  nlinarith [hinvψ, Real.goldenRatio_add_goldenConj]

lemma pom_golden_likelihood_ratio_martingales_inv_sq_eq_one_sub_inv :
    pom_golden_likelihood_ratio_martingales_plusProb ^ 2 =
      1 - pom_golden_likelihood_ratio_martingales_plusProb := by
  let x : ℝ := pom_golden_likelihood_ratio_martingales_plusProb
  have hx : x = Real.goldenRatio - 1 := by
    simpa [x, pom_golden_likelihood_ratio_martingales_plusProb] using
      pom_golden_likelihood_ratio_martingales_inv_eq_sub_one
  have hsq : x ^ 2 = 1 - x := by
    nlinarith [Real.goldenRatio_sq, hx]
  simpa [x]

lemma pom_golden_likelihood_ratio_martingales_stepRatio_eq_zpow (b : Bool) :
    pom_golden_likelihood_ratio_martingales_stepRatio b =
      Real.goldenRatio ^ pom_golden_likelihood_ratio_martingales_stepIncrement b := by
  cases b <;> simp [pom_golden_likelihood_ratio_martingales_stepRatio,
    pom_golden_likelihood_ratio_martingales_stepIncrement]

lemma pom_golden_likelihood_ratio_martingales_likelihoodRatio_eq_zpow (path : List Bool) :
    pom_golden_likelihood_ratio_martingales_likelihoodRatio path =
      Real.goldenRatio ^ pom_golden_likelihood_ratio_martingales_walkExponent path := by
  have hphi_ne : (Real.goldenRatio : ℝ) ≠ 0 := by
    exact ne_of_gt Real.goldenRatio_pos
  induction path with
  | nil =>
      simp [pom_golden_likelihood_ratio_martingales_likelihoodRatio,
        pom_golden_likelihood_ratio_martingales_walkExponent]
  | cons b bs ih =>
      rw [pom_golden_likelihood_ratio_martingales_likelihoodRatio,
        pom_golden_likelihood_ratio_martingales_walkExponent, ih,
        pom_golden_likelihood_ratio_martingales_stepRatio_eq_zpow]
      simpa [zpow_add₀ hphi_ne, add_comm, add_left_comm, add_assoc]

lemma pom_golden_likelihood_ratio_martingales_minus_one_step_expectation :
    pom_golden_likelihood_ratio_martingales_minusMass true *
        pom_golden_likelihood_ratio_martingales_stepRatio true +
      pom_golden_likelihood_ratio_martingales_minusMass false *
        pom_golden_likelihood_ratio_martingales_stepRatio false = 1 := by
  have hphi_ne : (Real.goldenRatio : ℝ) ≠ 0 := by
    exact ne_of_gt Real.goldenRatio_pos
  have hmul :
      pom_golden_likelihood_ratio_martingales_plusProb * Real.goldenRatio = 1 := by
    simpa [pom_golden_likelihood_ratio_martingales_plusProb] using inv_mul_cancel₀ hphi_ne
  calc
    pom_golden_likelihood_ratio_martingales_minusMass true *
          pom_golden_likelihood_ratio_martingales_stepRatio true +
        pom_golden_likelihood_ratio_martingales_minusMass false *
          pom_golden_likelihood_ratio_martingales_stepRatio false
        =
      pom_golden_likelihood_ratio_martingales_minusProb * Real.goldenRatio +
        pom_golden_likelihood_ratio_martingales_plusProb * Real.goldenRatio⁻¹ := by
          simp [pom_golden_likelihood_ratio_martingales_minusMass,
            pom_golden_likelihood_ratio_martingales_stepRatio]
    _ =
      pom_golden_likelihood_ratio_martingales_plusProb +
        pom_golden_likelihood_ratio_martingales_plusProb ^ 2 := by
          have hfirst :
              pom_golden_likelihood_ratio_martingales_minusProb * Real.goldenRatio =
                pom_golden_likelihood_ratio_martingales_plusProb := by
            calc
              pom_golden_likelihood_ratio_martingales_minusProb * Real.goldenRatio
                  = pom_golden_likelihood_ratio_martingales_plusProb *
                      (pom_golden_likelihood_ratio_martingales_plusProb * Real.goldenRatio) := by
                        simp [pom_golden_likelihood_ratio_martingales_minusProb]
                        ring
              _ = pom_golden_likelihood_ratio_martingales_plusProb * 1 := by rw [hmul]
              _ = pom_golden_likelihood_ratio_martingales_plusProb := by ring
          have hsecond :
              pom_golden_likelihood_ratio_martingales_plusProb * Real.goldenRatio⁻¹ =
                pom_golden_likelihood_ratio_martingales_plusProb ^ 2 := by
            calc
              pom_golden_likelihood_ratio_martingales_plusProb * Real.goldenRatio⁻¹
                  =
                pom_golden_likelihood_ratio_martingales_plusProb *
                  pom_golden_likelihood_ratio_martingales_plusProb := by
                    simp [pom_golden_likelihood_ratio_martingales_plusProb]
              _ = pom_golden_likelihood_ratio_martingales_plusProb ^ 2 := by ring
          rw [hfirst, hsecond]
    _ = 1 := by
          nlinarith [pom_golden_likelihood_ratio_martingales_inv_sq_eq_one_sub_inv]

lemma pom_golden_likelihood_ratio_martingales_plus_one_step_dual_expectation :
    pom_golden_likelihood_ratio_martingales_plusMass true *
        (pom_golden_likelihood_ratio_martingales_stepRatio true)⁻¹ +
      pom_golden_likelihood_ratio_martingales_plusMass false *
        (pom_golden_likelihood_ratio_martingales_stepRatio false)⁻¹ = 1 := by
  have hphi_ne : (Real.goldenRatio : ℝ) ≠ 0 := by
    exact ne_of_gt Real.goldenRatio_pos
  have hmul :
      pom_golden_likelihood_ratio_martingales_plusProb * Real.goldenRatio = 1 := by
    simpa [pom_golden_likelihood_ratio_martingales_plusProb] using inv_mul_cancel₀ hphi_ne
  calc
    pom_golden_likelihood_ratio_martingales_plusMass true *
          (pom_golden_likelihood_ratio_martingales_stepRatio true)⁻¹ +
        pom_golden_likelihood_ratio_martingales_plusMass false *
          (pom_golden_likelihood_ratio_martingales_stepRatio false)⁻¹
        =
      pom_golden_likelihood_ratio_martingales_plusProb * Real.goldenRatio⁻¹ +
        pom_golden_likelihood_ratio_martingales_minusProb * Real.goldenRatio := by
          simp [pom_golden_likelihood_ratio_martingales_plusMass,
            pom_golden_likelihood_ratio_martingales_stepRatio]
    _ =
      pom_golden_likelihood_ratio_martingales_plusProb ^ 2 +
        pom_golden_likelihood_ratio_martingales_plusProb := by
          have hfirst :
              pom_golden_likelihood_ratio_martingales_plusProb * Real.goldenRatio⁻¹ =
                pom_golden_likelihood_ratio_martingales_plusProb ^ 2 := by
            calc
              pom_golden_likelihood_ratio_martingales_plusProb * Real.goldenRatio⁻¹
                  =
                pom_golden_likelihood_ratio_martingales_plusProb *
                  pom_golden_likelihood_ratio_martingales_plusProb := by
                    simp [pom_golden_likelihood_ratio_martingales_plusProb]
              _ = pom_golden_likelihood_ratio_martingales_plusProb ^ 2 := by ring
          have hsecond :
              pom_golden_likelihood_ratio_martingales_minusProb * Real.goldenRatio =
                pom_golden_likelihood_ratio_martingales_plusProb := by
            calc
              pom_golden_likelihood_ratio_martingales_minusProb * Real.goldenRatio
                  = pom_golden_likelihood_ratio_martingales_plusProb *
                      (pom_golden_likelihood_ratio_martingales_plusProb * Real.goldenRatio) := by
                        simp [pom_golden_likelihood_ratio_martingales_minusProb]
                        ring
              _ = pom_golden_likelihood_ratio_martingales_plusProb * 1 := by rw [hmul]
              _ = pom_golden_likelihood_ratio_martingales_plusProb := by ring
          rw [hfirst, hsecond]
    _ = 1 := by
          nlinarith [pom_golden_likelihood_ratio_martingales_inv_sq_eq_one_sub_inv]

/-- Paper label: `prop:pom-golden-likelihood-ratio-martingales`. In the complementary Bernoulli
golden model, the likelihood ratio is exactly `φ^{K_n}`, the one-step conditional expectations
are `1` under the two phases, and every bounded stopped expectation coming from a stopping law on
`{0, …, N}` stays equal to `1`. -/
theorem paper_pom_golden_likelihood_ratio_martingales :
    (∀ path,
      pom_golden_likelihood_ratio_martingales_likelihoodRatio path =
        Real.goldenRatio ^ pom_golden_likelihood_ratio_martingales_walkExponent path) ∧
      (pom_golden_likelihood_ratio_martingales_minusMass true *
          pom_golden_likelihood_ratio_martingales_stepRatio true +
        pom_golden_likelihood_ratio_martingales_minusMass false *
          pom_golden_likelihood_ratio_martingales_stepRatio false = 1) ∧
      (pom_golden_likelihood_ratio_martingales_plusMass true *
          (pom_golden_likelihood_ratio_martingales_stepRatio true)⁻¹ +
        pom_golden_likelihood_ratio_martingales_plusMass false *
          (pom_golden_likelihood_ratio_martingales_stepRatio false)⁻¹ = 1) ∧
      (∀ n, pom_golden_likelihood_ratio_martingales_minusExpectation n = 1) ∧
      (∀ n, pom_golden_likelihood_ratio_martingales_plusDualExpectation n = 1) ∧
      (∀ N (ρ : pom_golden_likelihood_ratio_martingales_stoppingLaw N),
        (∑ i, ρ i = 1) →
          pom_golden_likelihood_ratio_martingales_stoppedMinusExpectation ρ = 1 ∧
            pom_golden_likelihood_ratio_martingales_stoppedPlusDualExpectation ρ = 1) := by
  have hminusAll : ∀ n, pom_golden_likelihood_ratio_martingales_minusExpectation n = 1 := by
    intro n
    induction n with
    | zero =>
        simp [pom_golden_likelihood_ratio_martingales_minusExpectation]
    | succ n ih =>
        simp [pom_golden_likelihood_ratio_martingales_minusExpectation, ih,
          pom_golden_likelihood_ratio_martingales_minus_one_step_expectation]
  have hplusAll : ∀ n, pom_golden_likelihood_ratio_martingales_plusDualExpectation n = 1 := by
    intro n
    induction n with
    | zero =>
        simp [pom_golden_likelihood_ratio_martingales_plusDualExpectation]
    | succ n ih =>
        simp [pom_golden_likelihood_ratio_martingales_plusDualExpectation, ih,
          pom_golden_likelihood_ratio_martingales_plus_one_step_dual_expectation]
  refine ⟨pom_golden_likelihood_ratio_martingales_likelihoodRatio_eq_zpow,
    pom_golden_likelihood_ratio_martingales_minus_one_step_expectation,
    pom_golden_likelihood_ratio_martingales_plus_one_step_dual_expectation,
    hminusAll, hplusAll, ?_⟩
  · intro N ρ hρ
    constructor
    · unfold pom_golden_likelihood_ratio_martingales_stoppedMinusExpectation
      calc
        ∑ i, ρ i * pom_golden_likelihood_ratio_martingales_minusExpectation i.1
            = ∑ i, ρ i * 1 := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [hminusAll i.1]
        _ = ∑ i, ρ i := by simp
        _ = 1 := hρ
    · unfold pom_golden_likelihood_ratio_martingales_stoppedPlusDualExpectation
      calc
        ∑ i, ρ i * pom_golden_likelihood_ratio_martingales_plusDualExpectation i.1
            = ∑ i, ρ i * 1 := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [hplusAll i.1]
        _ = ∑ i, ρ i := by simp
        _ = 1 := hρ

end Omega.POM
