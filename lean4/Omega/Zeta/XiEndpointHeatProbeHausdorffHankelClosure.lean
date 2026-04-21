import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The two endpoint masses used in the concrete Hausdorff/Hankel model. -/
def xiEndpointHeatProbeNodes (a b : ℝ) : Fin 2 → ℝ
  | 0 => a
  | 1 => b

/-- The positive atom weights of the concrete endpoint probe. -/
def xiEndpointHeatProbeWeights (w0 w1 : ℝ) : Fin 2 → ℝ
  | 0 => w0
  | 1 => w1

/-- The endpoint heat-probe moments are represented by a two-atom measure on `[0,1]`. -/
def xiEndpointHeatProbeMoment (a b w0 w1 : ℝ) (N : ℕ) : ℝ :=
  ∑ i : Fin 2, xiEndpointHeatProbeWeights w0 w1 i * xiEndpointHeatProbeNodes a b i ^ N

/-- Concrete Hausdorff moment-sequence witness for the endpoint probe. -/
def xiEndpointHeatProbeIsHausdorffMomentSequence (a b w0 w1 : ℝ) : Prop :=
  ∃ nodes weights : Fin 2 → ℝ,
    (∀ i, 0 ≤ nodes i ∧ nodes i ≤ 1) ∧
      (∀ i, 0 ≤ weights i) ∧
      ∀ N, xiEndpointHeatProbeMoment a b w0 w1 N = ∑ i : Fin 2, weights i * nodes i ^ N

/-- The quadratic form associated to the finite Hankel matrices of the concrete moment sequence. -/
def xiEndpointHeatProbeHankelQuadraticForm (a b w0 w1 : ℝ) (n : ℕ) (c : Fin n → ℝ) : ℝ :=
  ∑ j : Fin 2,
    xiEndpointHeatProbeWeights w0 w1 j *
      (∑ i : Fin n, c i * xiEndpointHeatProbeNodes a b j ^ (i : ℕ)) ^ 2

/-- Positive semidefiniteness of all finite Hankel forms for the concrete moment sequence. -/
def xiEndpointHeatProbeHankelPsd (a b w0 w1 : ℝ) : Prop :=
  ∀ n (c : Fin n → ℝ), 0 ≤ xiEndpointHeatProbeHankelQuadraticForm a b w0 w1 n c

/-- Hausdorff complete-monotonicity written as the alternating forward-difference integral. -/
def xiEndpointHeatProbeCompletelyMonotone (a b w0 w1 : ℝ) : Prop :=
  ∀ k m,
    0 ≤
      ∑ i : Fin 2,
        xiEndpointHeatProbeWeights w0 w1 i * xiEndpointHeatProbeNodes a b i ^ m *
          (1 - xiEndpointHeatProbeNodes a b i) ^ k

/-- Log-convexity of the endpoint heat-probe moment sequence. -/
def xiEndpointHeatProbeLogConvex (a b w0 w1 : ℝ) : Prop :=
  ∀ m,
    xiEndpointHeatProbeMoment a b w0 w1 (m + 1) ^ 2 ≤
      xiEndpointHeatProbeMoment a b w0 w1 m * xiEndpointHeatProbeMoment a b w0 w1 (m + 2)

/-- Consecutive ratios are monotone, and every ratio stays below the endpoint radius `1`. -/
def xiEndpointHeatProbeRatioMonotoneToRadius (a b w0 w1 : ℝ) : Prop :=
  ∀ m,
    xiEndpointHeatProbeMoment a b w0 w1 (m + 1) ^ 2 ≤
        xiEndpointHeatProbeMoment a b w0 w1 m * xiEndpointHeatProbeMoment a b w0 w1 (m + 2) ∧
      xiEndpointHeatProbeMoment a b w0 w1 (m + 1) ≤ xiEndpointHeatProbeMoment a b w0 w1 m

lemma xiEndpointHeatProbeMoment_eq_two_terms (a b w0 w1 : ℝ) (N : ℕ) :
    xiEndpointHeatProbeMoment a b w0 w1 N = w0 * a ^ N + w1 * b ^ N := by
  simp [xiEndpointHeatProbeMoment, xiEndpointHeatProbeWeights, xiEndpointHeatProbeNodes,
    Fin.sum_univ_two]

lemma xiEndpointHeatProbeLogConvex_gap_nonneg
    (a b w0 w1 : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (m : ℕ) :
    0 ≤
      xiEndpointHeatProbeMoment a b w0 w1 m * xiEndpointHeatProbeMoment a b w0 w1 (m + 2) -
        xiEndpointHeatProbeMoment a b w0 w1 (m + 1) ^ 2 := by
  rw [xiEndpointHeatProbeMoment_eq_two_terms, xiEndpointHeatProbeMoment_eq_two_terms,
    xiEndpointHeatProbeMoment_eq_two_terms]
  have ha1 : a ^ (m + 1) = a ^ m * a := by simp [pow_add]
  have hb1 : b ^ (m + 1) = b ^ m * b := by simp [pow_add]
  have ha2 : a ^ (m + 2) = a ^ m * a ^ 2 := by simp [pow_add]
  have hb2 : b ^ (m + 2) = b ^ m * b ^ 2 := by simp [pow_add]
  rw [ha1, hb1, ha2, hb2]
  have hmain :
      (w0 * a ^ m + w1 * b ^ m) * (w0 * (a ^ m * a ^ 2) + w1 * (b ^ m * b ^ 2)) -
          (w0 * (a ^ m * a) + w1 * (b ^ m * b)) ^ 2 =
        w0 * w1 * (a ^ m * b ^ m) * (a - b) ^ 2 := by
    ring
  rw [hmain]
  have hpowa : 0 ≤ a ^ m := pow_nonneg ha m
  have hpowb : 0 ≤ b ^ m := pow_nonneg hb m
  have hprod : 0 ≤ w0 * w1 * (a ^ m * b ^ m) := by
    exact mul_nonneg (mul_nonneg hw0 hw1) (mul_nonneg hpowa hpowb)
  exact mul_nonneg hprod (sq_nonneg (a - b))

lemma xiEndpointHeatProbeMoment_step_le
    (a b w0 w1 : ℝ) (ha : 0 ≤ a) (ha_one : a ≤ 1) (hb : 0 ≤ b) (hb_one : b ≤ 1)
    (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (m : ℕ) :
    xiEndpointHeatProbeMoment a b w0 w1 (m + 1) ≤ xiEndpointHeatProbeMoment a b w0 w1 m := by
  have hpowa : 0 ≤ a ^ m := pow_nonneg ha m
  have hpowb : 0 ≤ b ^ m := pow_nonneg hb m
  have hstepa : a ^ (m + 1) ≤ a ^ m := by
    rw [pow_add]
    simp only [pow_one]
    simpa using mul_le_mul_of_nonneg_left ha_one hpowa
  have hstepb : b ^ (m + 1) ≤ b ^ m := by
    rw [pow_add]
    simp only [pow_one]
    simpa using mul_le_mul_of_nonneg_left hb_one hpowb
  have hterm0 : w0 * a ^ (m + 1) ≤ w0 * a ^ m := mul_le_mul_of_nonneg_left hstepa hw0
  have hterm1 : w1 * b ^ (m + 1) ≤ w1 * b ^ m := mul_le_mul_of_nonneg_left hstepb hw1
  rw [xiEndpointHeatProbeMoment_eq_two_terms, xiEndpointHeatProbeMoment_eq_two_terms]
  linarith

/-- Paper label: `thm:xi-endpoint-heat-probe-hausdorff-hankel-closure`. A concrete two-atom
Hausdorff representation yields the Hankel positivity, complete monotonicity, log-convexity, and
ratio-to-radius monotonicity package for the endpoint heat-probe moment sequence. -/
theorem paper_xi_endpoint_heat_probe_hausdorff_hankel_closure
    (a b w0 w1 : ℝ) (ha : 0 ≤ a) (ha_lt : a < 1) (hb : 0 ≤ b) (hb_lt : b < 1)
    (hw0 : 0 < w0) (hw1 : 0 < w1) :
    xiEndpointHeatProbeIsHausdorffMomentSequence a b w0 w1 ∧
      xiEndpointHeatProbeHankelPsd a b w0 w1 ∧
      xiEndpointHeatProbeCompletelyMonotone a b w0 w1 ∧
      xiEndpointHeatProbeLogConvex a b w0 w1 ∧
      xiEndpointHeatProbeRatioMonotoneToRadius a b w0 w1 := by
  have hw0' : 0 ≤ w0 := le_of_lt hw0
  have hw1' : 0 ≤ w1 := le_of_lt hw1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨xiEndpointHeatProbeNodes a b, xiEndpointHeatProbeWeights w0 w1, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact ⟨ha, ha_lt.le⟩
      · exact ⟨hb, hb_lt.le⟩
    · intro i
      fin_cases i
      · exact hw0'
      · exact hw1'
    · intro N
      rfl
  · intro n c
    have h₀ :
        0 ≤
          w0 * (∑ i : Fin n, c i * a ^ (i : ℕ)) ^ 2 := by
      exact mul_nonneg hw0' (sq_nonneg _)
    have h₁ :
        0 ≤
          w1 * (∑ i : Fin n, c i * b ^ (i : ℕ)) ^ 2 := by
      exact mul_nonneg hw1' (sq_nonneg _)
    simpa [xiEndpointHeatProbeHankelQuadraticForm, xiEndpointHeatProbeWeights,
      xiEndpointHeatProbeNodes, Fin.sum_univ_two] using add_nonneg h₀ h₁
  · intro k m
    have h₀ :
        0 ≤ w0 * a ^ m * (1 - a) ^ k := by
      have hpowa : 0 ≤ a ^ m := pow_nonneg ha m
      have hpowtail : 0 ≤ (1 - a) ^ k := by
        have htail : 0 ≤ 1 - a := by linarith
        exact pow_nonneg htail k
      exact mul_nonneg (mul_nonneg hw0' hpowa) hpowtail
    have h₁ :
        0 ≤ w1 * b ^ m * (1 - b) ^ k := by
      have hpowb : 0 ≤ b ^ m := pow_nonneg hb m
      have hpowtail : 0 ≤ (1 - b) ^ k := by
        have htail : 0 ≤ 1 - b := by linarith
        exact pow_nonneg htail k
      exact mul_nonneg (mul_nonneg hw1' hpowb) hpowtail
    simpa [xiEndpointHeatProbeCompletelyMonotone, xiEndpointHeatProbeWeights,
      xiEndpointHeatProbeNodes, Fin.sum_univ_two] using add_nonneg h₀ h₁
  · intro m
    have hgap :=
      xiEndpointHeatProbeLogConvex_gap_nonneg a b w0 w1 ha hb hw0' hw1' m
    linarith
  · intro m
    refine ⟨?_, ?_⟩
    · exact (show xiEndpointHeatProbeLogConvex a b w0 w1 from by
        intro n
        have hgap :=
          xiEndpointHeatProbeLogConvex_gap_nonneg a b w0 w1 ha hb hw0' hw1' n
        linarith) m
    · exact xiEndpointHeatProbeMoment_step_le a b w0 w1 ha ha_lt.le hb hb_lt.le hw0' hw1' m

end Omega.Zeta
