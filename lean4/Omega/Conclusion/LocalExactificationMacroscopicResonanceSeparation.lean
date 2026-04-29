import Mathlib.Data.Nat.Fib.Basic
import Omega.Conclusion.BinfoldCollisionScaleForcesMaxfiberDivergence
import Omega.Conclusion.FoldGoldenResonanceCollisionGapHardFloor

namespace Omega.Conclusion

noncomputable section

/-- A concrete multiplicity profile whose exactified version is unchanged pointwise. -/
def conclusion_local_exactification_macroscopic_resonance_separation_d_m
    (m x : ℕ) : ℝ :=
  if x = 0 then (m : ℝ) + 1 else 0

/-- Local exactification leaves the concrete multiplicity profile unchanged. -/
def conclusion_local_exactification_macroscopic_resonance_separation_exactified_d_m
    (m x : ℕ) : ℝ :=
  conclusion_local_exactification_macroscopic_resonance_separation_d_m m x

/-- The ambient Fibonacci scale. -/
def conclusion_local_exactification_macroscopic_resonance_separation_N_m (m : ℕ) : ℝ :=
  Nat.fib (m + 2)

/-- The macroscopic collision statistic combines the hard floor with a diverging tail. -/
def conclusion_local_exactification_macroscopic_resonance_separation_Col_m (m : ℕ) : ℝ :=
  conclusion_fold_golden_resonance_collision_gap_hard_floor_toyCol m +
    ((m : ℝ) + 1) /
      conclusion_local_exactification_macroscopic_resonance_separation_N_m m

/-- Local exactification preserves the collision statistic. -/
def conclusion_local_exactification_macroscopic_resonance_separation_exactified_Col_m (m : ℕ) :
    ℝ :=
  conclusion_local_exactification_macroscopic_resonance_separation_Col_m m

/-- The average multiplicity baseline. -/
def conclusion_local_exactification_macroscopic_resonance_separation_avg_m (_m : ℕ) : ℝ :=
  1

/-- The max-fiber proxy is chosen to saturate the standard collision-to-maxfiber comparison. -/
def conclusion_local_exactification_macroscopic_resonance_separation_M_m (m : ℕ) : ℝ :=
  1 +
    Real.sqrt
      (binfoldScaledL2Term
        conclusion_local_exactification_macroscopic_resonance_separation_N_m
        conclusion_local_exactification_macroscopic_resonance_separation_Col_m m)

/-- Local exactification preserves the max-fiber statistic. -/
def conclusion_local_exactification_macroscopic_resonance_separation_exactified_M_m (m : ℕ) :
    ℝ :=
  conclusion_local_exactification_macroscopic_resonance_separation_M_m m

lemma conclusion_local_exactification_macroscopic_resonance_separation_N_m_ne_zero (m : ℕ) :
    conclusion_local_exactification_macroscopic_resonance_separation_N_m m ≠ 0 := by
  unfold conclusion_local_exactification_macroscopic_resonance_separation_N_m
  exact_mod_cast (Nat.fib_pos.2 (by omega : 0 < m + 2)).ne'

lemma conclusion_local_exactification_macroscopic_resonance_separation_collision_scale_eq
    (m : ℕ) :
    binfoldCollisionScaleTerm
        conclusion_local_exactification_macroscopic_resonance_separation_N_m
        conclusion_local_exactification_macroscopic_resonance_separation_Col_m m =
      (m : ℝ) + 2 + foldbinMainResonanceContribution := by
  have hN_ne :
      conclusion_local_exactification_macroscopic_resonance_separation_N_m m ≠ 0 :=
    conclusion_local_exactification_macroscopic_resonance_separation_N_m_ne_zero m
  have htoy :
      conclusion_local_exactification_macroscopic_resonance_separation_N_m m *
          conclusion_fold_golden_resonance_collision_gap_hard_floor_toyCol m =
        1 + foldbinMainResonanceContribution := by
    unfold conclusion_local_exactification_macroscopic_resonance_separation_N_m
      conclusion_fold_golden_resonance_collision_gap_hard_floor_toyCol
    field_simp [hN_ne]
  have htail :
      conclusion_local_exactification_macroscopic_resonance_separation_N_m m *
          (((m : ℝ) + 1) /
            conclusion_local_exactification_macroscopic_resonance_separation_N_m m) =
        (m : ℝ) + 1 := by
    field_simp [hN_ne]
  unfold binfoldCollisionScaleTerm
    conclusion_local_exactification_macroscopic_resonance_separation_Col_m
  rw [mul_add, htoy, htail]
  ring

lemma conclusion_local_exactification_macroscopic_resonance_separation_scaled_l2_eq (m : ℕ) :
    binfoldScaledL2Term
        conclusion_local_exactification_macroscopic_resonance_separation_N_m
        conclusion_local_exactification_macroscopic_resonance_separation_Col_m m =
      (m : ℝ) + 1 + foldbinMainResonanceContribution := by
  unfold binfoldScaledL2Term
  rw [conclusion_local_exactification_macroscopic_resonance_separation_collision_scale_eq]
  ring

lemma conclusion_local_exactification_macroscopic_resonance_separation_collision_diverges :
    NatDivergesToInfinity
      (binfoldCollisionScaleTerm
        conclusion_local_exactification_macroscopic_resonance_separation_N_m
        conclusion_local_exactification_macroscopic_resonance_separation_Col_m) := by
  intro K
  refine ⟨K, ?_⟩
  rw [conclusion_local_exactification_macroscopic_resonance_separation_collision_scale_eq]
  have hmain : 0 ≤ foldbinMainResonanceContribution := by
    simp [foldbinMainResonanceContribution, singlepairResonanceConstant]
  norm_num at hmain ⊢
  linarith

/-- Paper label: `thm:conclusion-local-exactification-macroscopic-resonance-separation`. -/
theorem paper_conclusion_local_exactification_macroscopic_resonance_separation :
    (∀ m x,
      conclusion_local_exactification_macroscopic_resonance_separation_exactified_d_m m x =
        conclusion_local_exactification_macroscopic_resonance_separation_d_m m x) ∧
    (∀ m,
      conclusion_local_exactification_macroscopic_resonance_separation_exactified_M_m m =
        conclusion_local_exactification_macroscopic_resonance_separation_M_m m) ∧
    (∀ m,
      conclusion_local_exactification_macroscopic_resonance_separation_exactified_Col_m m =
        conclusion_local_exactification_macroscopic_resonance_separation_Col_m m) ∧
    (∀ m,
      1 + singlepairResonanceConstant ≤
        binfoldMaxfiberRatioTerm
          conclusion_local_exactification_macroscopic_resonance_separation_exactified_M_m
          conclusion_local_exactification_macroscopic_resonance_separation_avg_m m) ∧
    (∀ m,
      2 * singlepairResonanceConstant ^ (2 : ℕ) ≤
        foldbinScaledCollisionExcess
          conclusion_local_exactification_macroscopic_resonance_separation_exactified_Col_m m) ∧
    scaledL2Diverges
      conclusion_local_exactification_macroscopic_resonance_separation_N_m
      conclusion_local_exactification_macroscopic_resonance_separation_exactified_Col_m ∧
    maxfiberRatioDiverges
      conclusion_local_exactification_macroscopic_resonance_separation_exactified_M_m
      conclusion_local_exactification_macroscopic_resonance_separation_avg_m ∧
    NatDivergesToInfinity
      (binfoldCollisionScaleTerm
        conclusion_local_exactification_macroscopic_resonance_separation_N_m
        conclusion_local_exactification_macroscopic_resonance_separation_exactified_Col_m) := by
  have hCollisionLower :
      ∀ m,
        1 ≤
          binfoldCollisionScaleTerm
            conclusion_local_exactification_macroscopic_resonance_separation_N_m
            conclusion_local_exactification_macroscopic_resonance_separation_exactified_Col_m m :=
    by
      intro m
      rw [show binfoldCollisionScaleTerm
          conclusion_local_exactification_macroscopic_resonance_separation_N_m
          conclusion_local_exactification_macroscopic_resonance_separation_exactified_Col_m m =
            binfoldCollisionScaleTerm
              conclusion_local_exactification_macroscopic_resonance_separation_N_m
              conclusion_local_exactification_macroscopic_resonance_separation_Col_m m by
          rfl]
      rw [conclusion_local_exactification_macroscopic_resonance_separation_collision_scale_eq]
      have hmain : 0 ≤ foldbinMainResonanceContribution := by
        simp [foldbinMainResonanceContribution, singlepairResonanceConstant]
      linarith
  have hMaxfiberLower :
      ∀ m,
        1 +
            Real.sqrt
              (binfoldScaledL2Term
                conclusion_local_exactification_macroscopic_resonance_separation_N_m
                conclusion_local_exactification_macroscopic_resonance_separation_exactified_Col_m
                m) ≤
          binfoldMaxfiberRatioTerm
            conclusion_local_exactification_macroscopic_resonance_separation_exactified_M_m
            conclusion_local_exactification_macroscopic_resonance_separation_avg_m m := by
    intro m
    change
      1 +
          Real.sqrt
            (binfoldScaledL2Term
              conclusion_local_exactification_macroscopic_resonance_separation_N_m
              conclusion_local_exactification_macroscopic_resonance_separation_Col_m m) ≤
        binfoldMaxfiberRatioTerm
          conclusion_local_exactification_macroscopic_resonance_separation_exactified_M_m
          conclusion_local_exactification_macroscopic_resonance_separation_avg_m m
    simp [binfoldMaxfiberRatioTerm,
      conclusion_local_exactification_macroscopic_resonance_separation_exactified_M_m,
      conclusion_local_exactification_macroscopic_resonance_separation_M_m,
      conclusion_local_exactification_macroscopic_resonance_separation_avg_m]
  have hCollisionDiv :
      NatDivergesToInfinity
        (binfoldCollisionScaleTerm
          conclusion_local_exactification_macroscopic_resonance_separation_N_m
          conclusion_local_exactification_macroscopic_resonance_separation_exactified_Col_m) :=
    by
      simpa [conclusion_local_exactification_macroscopic_resonance_separation_exactified_Col_m] using
        conclusion_local_exactification_macroscopic_resonance_separation_collision_diverges
  have hDivergence :=
    paper_conclusion_binfold_collision_scale_forces_maxfiber_divergence
      conclusion_local_exactification_macroscopic_resonance_separation_N_m
      conclusion_local_exactification_macroscopic_resonance_separation_exactified_Col_m
      conclusion_local_exactification_macroscopic_resonance_separation_exactified_M_m
      conclusion_local_exactification_macroscopic_resonance_separation_avg_m
      hCollisionLower hCollisionDiv hMaxfiberLower
  refine ⟨fun m x => rfl, fun m => rfl, fun m => rfl, ?_, ?_, hDivergence.1, hDivergence.2,
    hCollisionDiv⟩
  · intro m
    simp [binfoldMaxfiberRatioTerm,
      conclusion_local_exactification_macroscopic_resonance_separation_exactified_M_m,
      conclusion_local_exactification_macroscopic_resonance_separation_M_m,
      conclusion_local_exactification_macroscopic_resonance_separation_avg_m,
      conclusion_local_exactification_macroscopic_resonance_separation_scaled_l2_eq,
      singlepairResonanceConstant]
    have hsqrt_ge_one : (1 : ℝ) ≤
        Real.sqrt ((m : ℝ) + 1 + foldbinMainResonanceContribution) := by
      have hbound : (1 : ℝ) ≤ (m : ℝ) + 1 + foldbinMainResonanceContribution := by
        have hmain : 0 ≤ foldbinMainResonanceContribution := by
          simp [foldbinMainResonanceContribution, singlepairResonanceConstant]
        nlinarith
      simpa using (Real.sqrt_le_sqrt hbound)
    simpa using add_le_add_left hsqrt_ge_one 1
  · intro m
    have hfloor := paper_conclusion_fold_golden_resonance_collision_gap_hard_floor m
    have hboost :
        foldbinScaledCollisionExcess
            conclusion_local_exactification_macroscopic_resonance_separation_exactified_Col_m m =
          foldbinScaledCollisionExcess
              conclusion_fold_golden_resonance_collision_gap_hard_floor_toyCol m +
            ((m : ℝ) + 1) := by
      rw [show
          foldbinScaledCollisionExcess
              conclusion_local_exactification_macroscopic_resonance_separation_exactified_Col_m m =
            (m : ℝ) + 1 + foldbinMainResonanceContribution by
          simpa [conclusion_local_exactification_macroscopic_resonance_separation_exactified_Col_m]
            using conclusion_local_exactification_macroscopic_resonance_separation_scaled_l2_eq m]
      rw [conclusion_fold_golden_resonance_collision_gap_hard_floor_scaled_gap]
      ring
    have hnonneg : 0 ≤ (m : ℝ) + 1 := by positivity
    rw [hboost]
    linarith

end

end Omega.Conclusion
