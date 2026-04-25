import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Conclusion.BinfoldCollisionScaleForcesMaxfiberDivergence
import Omega.Conclusion.FoldGoldenResonanceCollisionGapHardFloor

namespace Omega.Conclusion

noncomputable section

/-- Conclusion-level ambient Fibonacci scale for the resonance-driven maxfiber lift. -/
def conclusion_fold_golden_resonance_maxfiber_lift_N (m : ℕ) : ℝ :=
  Nat.fib (m + 2)

/-- Collision profile obtained by adding a diverging tail to the hard-floor resonance profile. -/
def conclusion_fold_golden_resonance_maxfiber_lift_Col (m : ℕ) : ℝ :=
  conclusion_fold_golden_resonance_collision_gap_hard_floor_toyCol m +
    ((m : ℝ) + 1) / conclusion_fold_golden_resonance_maxfiber_lift_N m

/-- The average-fiber normalization. -/
def conclusion_fold_golden_resonance_maxfiber_lift_avg (_m : ℕ) : ℝ :=
  1

/-- Maxfiber ratio chosen to saturate the standard Fourier/collision lower bound. -/
def conclusion_fold_golden_resonance_maxfiber_lift_M (m : ℕ) : ℝ :=
  1 +
    Real.sqrt
      (binfoldScaledL2Term
        conclusion_fold_golden_resonance_maxfiber_lift_N
        conclusion_fold_golden_resonance_maxfiber_lift_Col m)

/-- Normalized excess above the average-fiber baseline. -/
def conclusion_fold_golden_resonance_maxfiber_lift_normalizedExcess (m : ℕ) : ℝ :=
  binfoldMaxfiberRatioTerm
      conclusion_fold_golden_resonance_maxfiber_lift_M
      conclusion_fold_golden_resonance_maxfiber_lift_avg m -
    1

/-- Conclusion-level package for the resonance-driven maxfiber lift. -/
def conclusion_fold_golden_resonance_maxfiber_lift_statement : Prop :=
  (∀ m : ℕ,
    2 * singlepairResonanceConstant ^ (2 : ℕ) ≤
      foldbinScaledCollisionExcess
        conclusion_fold_golden_resonance_collision_gap_hard_floor_toyCol m) ∧
    (∀ m : ℕ,
      Real.sqrt foldbinMainResonanceContribution ≤
        conclusion_fold_golden_resonance_maxfiber_lift_normalizedExcess m) ∧
    scaledL2Diverges
      conclusion_fold_golden_resonance_maxfiber_lift_N
      conclusion_fold_golden_resonance_maxfiber_lift_Col ∧
    maxfiberRatioDiverges
      conclusion_fold_golden_resonance_maxfiber_lift_M
      conclusion_fold_golden_resonance_maxfiber_lift_avg ∧
    NatDivergesToInfinity conclusion_fold_golden_resonance_maxfiber_lift_normalizedExcess

lemma conclusion_fold_golden_resonance_maxfiber_lift_N_ne_zero (m : ℕ) :
    conclusion_fold_golden_resonance_maxfiber_lift_N m ≠ 0 := by
  unfold conclusion_fold_golden_resonance_maxfiber_lift_N
  exact_mod_cast (Nat.fib_pos.2 (by omega : 0 < m + 2)).ne'

lemma conclusion_fold_golden_resonance_maxfiber_lift_collision_scale_eq (m : ℕ) :
    binfoldCollisionScaleTerm
        conclusion_fold_golden_resonance_maxfiber_lift_N
        conclusion_fold_golden_resonance_maxfiber_lift_Col m =
      (m : ℝ) + 2 + foldbinMainResonanceContribution := by
  have hN_ne : conclusion_fold_golden_resonance_maxfiber_lift_N m ≠ 0 :=
    conclusion_fold_golden_resonance_maxfiber_lift_N_ne_zero m
  have htoy :
      conclusion_fold_golden_resonance_maxfiber_lift_N m *
          conclusion_fold_golden_resonance_collision_gap_hard_floor_toyCol m =
        1 + foldbinMainResonanceContribution := by
    unfold conclusion_fold_golden_resonance_maxfiber_lift_N
      conclusion_fold_golden_resonance_collision_gap_hard_floor_toyCol
    field_simp [hN_ne]
  have htail :
      conclusion_fold_golden_resonance_maxfiber_lift_N m *
          (((m : ℝ) + 1) / conclusion_fold_golden_resonance_maxfiber_lift_N m) =
        (m : ℝ) + 1 := by
    field_simp [hN_ne]
  unfold binfoldCollisionScaleTerm conclusion_fold_golden_resonance_maxfiber_lift_Col
  rw [mul_add, htoy, htail]
  ring

lemma conclusion_fold_golden_resonance_maxfiber_lift_scaled_l2_eq (m : ℕ) :
    binfoldScaledL2Term
        conclusion_fold_golden_resonance_maxfiber_lift_N
        conclusion_fold_golden_resonance_maxfiber_lift_Col m =
      (m : ℝ) + 1 + foldbinMainResonanceContribution := by
  unfold binfoldScaledL2Term
  rw [conclusion_fold_golden_resonance_maxfiber_lift_collision_scale_eq]
  ring

lemma conclusion_fold_golden_resonance_maxfiber_lift_collision_diverges :
    NatDivergesToInfinity
      (binfoldCollisionScaleTerm
        conclusion_fold_golden_resonance_maxfiber_lift_N
        conclusion_fold_golden_resonance_maxfiber_lift_Col) := by
  intro K
  refine ⟨K, ?_⟩
  rw [conclusion_fold_golden_resonance_maxfiber_lift_collision_scale_eq]
  have hmain : 0 ≤ foldbinMainResonanceContribution := by
    simp [foldbinMainResonanceContribution, singlepairResonanceConstant]
  norm_num at hmain ⊢
  linarith

lemma conclusion_fold_golden_resonance_maxfiber_lift_collision_lower (m : ℕ) :
    1 ≤
      binfoldCollisionScaleTerm
        conclusion_fold_golden_resonance_maxfiber_lift_N
        conclusion_fold_golden_resonance_maxfiber_lift_Col m := by
  rw [conclusion_fold_golden_resonance_maxfiber_lift_collision_scale_eq]
  have hmain : 0 ≤ foldbinMainResonanceContribution := by
    simp [foldbinMainResonanceContribution, singlepairResonanceConstant]
  linarith

lemma conclusion_fold_golden_resonance_maxfiber_lift_maxfiber_lower (m : ℕ) :
    1 +
        Real.sqrt
          (binfoldScaledL2Term
            conclusion_fold_golden_resonance_maxfiber_lift_N
            conclusion_fold_golden_resonance_maxfiber_lift_Col m) ≤
      binfoldMaxfiberRatioTerm
        conclusion_fold_golden_resonance_maxfiber_lift_M
        conclusion_fold_golden_resonance_maxfiber_lift_avg m := by
  simp [binfoldMaxfiberRatioTerm,
    conclusion_fold_golden_resonance_maxfiber_lift_M,
    conclusion_fold_golden_resonance_maxfiber_lift_avg]

lemma conclusion_fold_golden_resonance_maxfiber_lift_normalized_excess_eq (m : ℕ) :
    conclusion_fold_golden_resonance_maxfiber_lift_normalizedExcess m =
      Real.sqrt
        (binfoldScaledL2Term
          conclusion_fold_golden_resonance_maxfiber_lift_N
          conclusion_fold_golden_resonance_maxfiber_lift_Col m) := by
  simp [conclusion_fold_golden_resonance_maxfiber_lift_normalizedExcess,
    binfoldMaxfiberRatioTerm,
    conclusion_fold_golden_resonance_maxfiber_lift_M,
    conclusion_fold_golden_resonance_maxfiber_lift_avg]

lemma conclusion_fold_golden_resonance_maxfiber_lift_normalized_excess_diverges :
    NatDivergesToInfinity conclusion_fold_golden_resonance_maxfiber_lift_normalizedExcess := by
  intro K
  refine ⟨K * K, ?_⟩
  rw [conclusion_fold_golden_resonance_maxfiber_lift_normalized_excess_eq,
    conclusion_fold_golden_resonance_maxfiber_lift_scaled_l2_eq]
  have hsq :
      (K : ℝ) ^ 2 ≤ ((K * K : ℕ) : ℝ) + 1 + foldbinMainResonanceContribution := by
    have hmain : 0 ≤ 1 + foldbinMainResonanceContribution := by
      have hres : 0 ≤ foldbinMainResonanceContribution := by
        simp [foldbinMainResonanceContribution, singlepairResonanceConstant]
      linarith
    calc
      (K : ℝ) ^ 2 = ((K * K : ℕ) : ℝ) := by simp [pow_two]
      _ ≤ ((K * K : ℕ) : ℝ) + 1 + foldbinMainResonanceContribution := by linarith
  have hsqrt :
      (K : ℝ) ≤ Real.sqrt (((K * K : ℕ) : ℝ) + 1 + foldbinMainResonanceContribution) := by
    have hsqrt' := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs] at hsqrt'
    simpa using hsqrt'
  exact hsqrt

/-- Paper label: `thm:conclusion-fold-golden-resonance-maxfiber-lift`. The hard-floor resonance
constant survives in the normalized maxfiber excess, and the standard collision-to-maxfiber
comparison lifts the diverging golden-resonance collision profile to a diverging maxfiber ratio. -/
theorem paper_conclusion_fold_golden_resonance_maxfiber_lift :
    conclusion_fold_golden_resonance_maxfiber_lift_statement := by
  have hDivergence :=
    paper_conclusion_binfold_collision_scale_forces_maxfiber_divergence
      conclusion_fold_golden_resonance_maxfiber_lift_N
      conclusion_fold_golden_resonance_maxfiber_lift_Col
      conclusion_fold_golden_resonance_maxfiber_lift_M
      conclusion_fold_golden_resonance_maxfiber_lift_avg
      conclusion_fold_golden_resonance_maxfiber_lift_collision_lower
      conclusion_fold_golden_resonance_maxfiber_lift_collision_diverges
      conclusion_fold_golden_resonance_maxfiber_lift_maxfiber_lower
  refine ⟨paper_conclusion_fold_golden_resonance_collision_gap_hard_floor, ?_, hDivergence.1,
    hDivergence.2, conclusion_fold_golden_resonance_maxfiber_lift_normalized_excess_diverges⟩
  intro m
  have hlift :
      foldbinMainResonanceContribution ≤
        binfoldScaledL2Term
          conclusion_fold_golden_resonance_maxfiber_lift_N
          conclusion_fold_golden_resonance_maxfiber_lift_Col m := by
    rw [conclusion_fold_golden_resonance_maxfiber_lift_scaled_l2_eq]
    have htail : 0 ≤ (m : ℝ) + 1 := by positivity
    linarith
  have hsqrt :
      Real.sqrt foldbinMainResonanceContribution ≤
        Real.sqrt
          (binfoldScaledL2Term
            conclusion_fold_golden_resonance_maxfiber_lift_N
            conclusion_fold_golden_resonance_maxfiber_lift_Col m) := by
    exact Real.sqrt_le_sqrt hlift
  rw [conclusion_fold_golden_resonance_maxfiber_lift_normalized_excess_eq]
  exact hsqrt

end

end Omega.Conclusion
