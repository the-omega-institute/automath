import Mathlib.Tactic
import Omega.SPG.GraphEnergyEllipsoidGodelCodelengthDual

namespace Omega.SPG

/-- The weighted dual coefficient appearing in the sharp ellipsoid bound. -/
noncomputable def fold_godel_ellipsoid_duality_optimal_pairing_weightedBound {rank : ℕ}
    (w logp : Fin rank → ℝ) : ℝ :=
  ∑ i, (logp i) ^ 2 / w i

/-- The proportional maximizer suggested by weighted Cauchy-Schwarz. -/
noncomputable def fold_godel_ellipsoid_duality_optimal_pairing_maximizer {rank : ℕ} (radius : ℝ)
    (w logp : Fin rank → ℝ) : Fin rank → ℝ :=
  fun i =>
    radius * (logp i / w i) /
      Real.sqrt (fold_godel_ellipsoid_duality_optimal_pairing_weightedBound w logp)

/-- Concrete duality package for the weighted ellipsoid bound: a sharp upper bound, an explicit
proportional maximizer for the linear readout, and monotonicity of the weighted coefficient with
respect to coordinatewise growth of the logarithmic weights.
    thm:fold-godel-ellipsoid-duality-optimal-pairing -/
def fold_godel_ellipsoid_duality_optimal_pairing_claim (rank : Nat) (radius : Real)
    (w logp : Fin rank -> Real) : Prop :=
  (0 ≤ radius →
    (∀ i, 0 < w i) →
    ∀ x : Fin rank → Real,
      (∑ i, w i * x i ^ 2) ≤ radius ^ 2 →
        graphEnergyEllipsoidLogLength logp x ≤
          radius * Real.sqrt (fold_godel_ellipsoid_duality_optimal_pairing_weightedBound w logp)) ∧
  (0 ≤ radius →
    (∀ i, 0 < w i) →
    0 < fold_godel_ellipsoid_duality_optimal_pairing_weightedBound w logp →
      graphEnergyEllipsoidLogLength logp
          (fold_godel_ellipsoid_duality_optimal_pairing_maximizer radius w logp) =
        radius * Real.sqrt (fold_godel_ellipsoid_duality_optimal_pairing_weightedBound w logp)) ∧
  ((∀ i, 0 < w i) →
    ∀ logp' : Fin rank → Real,
      (∀ i, (logp i) ^ 2 ≤ (logp' i) ^ 2) →
        fold_godel_ellipsoid_duality_optimal_pairing_weightedBound w logp ≤
          fold_godel_ellipsoid_duality_optimal_pairing_weightedBound w logp')

theorem paper_fold_godel_ellipsoid_duality_optimal_pairing (rank : Nat) (radius : Real)
    (w logp : Fin rank -> Real) : fold_godel_ellipsoid_duality_optimal_pairing_claim rank radius w logp := by
  constructor
  · intro hr hw x hx
    let scaledX : Fin rank → ℝ := fun i => Real.sqrt (w i) * x i
    let scaledLog : Fin rank → ℝ := fun i => logp i / Real.sqrt (w i)
    have hw_nonneg : ∀ i, 0 ≤ w i := fun i => le_of_lt (hw i)
    have hmem : graphEnergyInEllipsoid (radius ^ 2) scaledX := by
      refine ⟨sq_nonneg radius, ?_⟩
      calc
        graphEnergyEllipsoidEnergy scaledX
            = ∑ i, (Real.sqrt (w i) * x i) ^ 2 := by
                simp [graphEnergyEllipsoidEnergy, scaledX]
        _ = ∑ i, w i * x i ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [mul_pow, Real.sq_sqrt (hw_nonneg i)]
        _ ≤ radius ^ 2 := hx
    have hdual :=
      paper_graph_energy_ellipsoid_godel_codelength_dual rank (radius ^ 2) scaledLog scaledX hmem
    have hlog :
        graphEnergyEllipsoidLogLength scaledLog scaledX = graphEnergyEllipsoidLogLength logp x := by
      unfold graphEnergyEllipsoidLogLength
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hsqrt_ne : Real.sqrt (w i) ≠ 0 := by
        exact ne_of_gt (Real.sqrt_pos.mpr (hw i))
      calc
        scaledLog i * scaledX i = (logp i / Real.sqrt (w i)) * (Real.sqrt (w i) * x i) := by
          rfl
        _ = logp i * x i := by
          field_simp [hsqrt_ne]
    have hbound :
        graphEnergyEllipsoidDualBound scaledLog =
          fold_godel_ellipsoid_duality_optimal_pairing_weightedBound w logp := by
      unfold graphEnergyEllipsoidDualBound
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [show scaledLog i = logp i / Real.sqrt (w i) by rfl, div_pow, Real.sq_sqrt (hw_nonneg i)]
    have habs :
        |graphEnergyEllipsoidLogLength logp x| ≤
          radius * Real.sqrt (fold_godel_ellipsoid_duality_optimal_pairing_weightedBound w logp) := by
      simpa [hlog, hbound, Real.sqrt_sq_eq_abs, abs_of_nonneg hr] using hdual
    exact le_trans (le_abs_self _) habs
  constructor
  · intro hr hw hbound_pos
    let s := fold_godel_ellipsoid_duality_optimal_pairing_weightedBound w logp
    have hs_nonneg : 0 ≤ s := by
      unfold s fold_godel_ellipsoid_duality_optimal_pairing_weightedBound
      exact Finset.sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (le_of_lt (hw i))
    have hsqrt_ne : Real.sqrt s ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.mpr hbound_pos)
    have hw_ne : ∀ i, w i ≠ 0 := fun i => ne_of_gt (hw i)
    calc
      graphEnergyEllipsoidLogLength logp
          (fold_godel_ellipsoid_duality_optimal_pairing_maximizer radius w logp)
          = ∑ i, (radius / Real.sqrt s) * ((logp i) ^ 2 / w i) := by
              unfold graphEnergyEllipsoidLogLength
              refine Finset.sum_congr rfl ?_
              intro i hi
              calc
                logp i * fold_godel_ellipsoid_duality_optimal_pairing_maximizer radius w logp i
                    = logp i * (radius * (logp i / w i) / Real.sqrt s) := by
                        simp [fold_godel_ellipsoid_duality_optimal_pairing_maximizer, s]
                _ = (radius / Real.sqrt s) * ((logp i) ^ 2 / w i) := by
                      field_simp [hw_ne i, hsqrt_ne]
                      
      _ = (radius / Real.sqrt s) * ∑ i, (logp i) ^ 2 / w i := by
            rw [Finset.mul_sum]
      _ = (radius / Real.sqrt s) * s := by
            have hs_eq : ∑ i, logp i ^ 2 / w i = s := by
              rfl
            rw [hs_eq]
      _ = radius * Real.sqrt s := by
            have hs_div : s / Real.sqrt s = Real.sqrt s := by
              apply (div_eq_iff hsqrt_ne).2
              simpa [pow_two, mul_comm] using (Real.sq_sqrt hs_nonneg).symm
            calc
              (radius / Real.sqrt s) * s = radius * (s / Real.sqrt s) := by
                  field_simp [hsqrt_ne]
              _ = radius * Real.sqrt s := by rw [hs_div]
      _ = radius * Real.sqrt (fold_godel_ellipsoid_duality_optimal_pairing_weightedBound w logp) := by
            rfl
  · intro hw logp' hlogp
    unfold fold_godel_ellipsoid_duality_optimal_pairing_weightedBound
    refine Finset.sum_le_sum ?_
    intro i hi
    have h_inv_nonneg : 0 ≤ (w i)⁻¹ := inv_nonneg.mpr (le_of_lt (hw i))
    have hscaled := mul_le_mul_of_nonneg_right (hlogp i) h_inv_nonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled

end Omega.SPG
