import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

open Filter
open scoped BigOperators Topology

noncomputable section

/-- The normalized log-pressure at a finite layer. -/
noncomputable def
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_pressureTerm
    (S : ℕ → ℝ) (m : ℕ) : ℝ :=
  Real.log (S m) / (m : ℝ)

/-- The two-level Wulff ray power sum, written before extracting the common small-fiber
power. -/
noncomputable def
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_powerSum
    (Fm am : ℕ) (smallPow eta : ℝ) : ℝ :=
  (am : ℝ) * (smallPow * (1 + eta)) + ((Fm - am : ℕ) : ℝ) * smallPow

/-- The extracted layer factor `F_m + a_m eta`. -/
noncomputable def
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor
    (Fm am : ℕ) (eta : ℝ) : ℝ :=
  (Fm : ℝ) + (am : ℝ) * eta

/-- Per-large-fiber escort mass after the common small-fiber power cancels. -/
noncomputable def
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_largeMass
    (Fm am : ℕ) (eta : ℝ) : ℝ :=
  (1 + eta) /
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor Fm am eta

/-- Per-small-fiber escort mass after the common small-fiber power cancels. -/
noncomputable def
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_smallMass
    (Fm am : ℕ) (eta : ℝ) : ℝ :=
  1 / conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor Fm am eta

/-- Uniform mass on a layer of size `F_m`. -/
noncomputable def
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_uniformMass
    (Fm : ℕ) : ℝ :=
  1 / (Fm : ℝ)

/-- The total variation distance obtained by aggregating the two fiber levels. -/
noncomputable def
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_twoLevelTV
    (Fm am : ℕ) (eta : ℝ) : ℝ :=
  ((am : ℝ) *
      |conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_largeMass Fm am eta -
        conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_uniformMass Fm| +
    ((Fm - am : ℕ) : ℝ) *
      |conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_smallMass Fm am eta -
        conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_uniformMass Fm|) /
    2

/-- The closed two-level total variation formula. -/
noncomputable def
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_tvFormula
    (Fm am : ℕ) (eta : ℝ) : ℝ :=
  (am : ℝ) * ((Fm : ℝ) - (am : ℝ)) * eta /
    ((Fm : ℝ) *
      conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor Fm am eta)

lemma
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_powerSum_factor
    {Fm am : ℕ} (ham : am ≤ Fm) (smallPow eta : ℝ) :
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_powerSum
        Fm am smallPow eta =
      smallPow *
        conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor
          Fm am eta := by
  unfold conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_powerSum
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor
  rw [Nat.cast_sub ham]
  ring_nf

lemma
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_large_diff
    {Fm am : ℕ} (hFm : 0 < Fm) {eta : ℝ}
    (hden :
      conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor
        Fm am eta ≠ 0) :
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_largeMass Fm am eta -
        conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_uniformMass Fm =
      eta * ((Fm : ℝ) - (am : ℝ)) /
        ((Fm : ℝ) *
          conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor
            Fm am eta) := by
  have hFne : (Fm : ℝ) ≠ 0 := by exact_mod_cast hFm.ne'
  have hden' : (Fm : ℝ) + (am : ℝ) * eta ≠ 0 := by
    simpa [conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor] using hden
  have hden'' : eta * (am : ℝ) + (Fm : ℝ) ≠ 0 := by
    simpa [add_comm, mul_comm, mul_left_comm] using hden'
  unfold conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_largeMass
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_uniformMass
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor
  field_simp [hFne, hden', hden'']
  have hdenD : (Fm : ℝ) + eta * (am : ℝ) ≠ 0 := by
    simpa [add_comm, mul_comm, mul_left_comm] using hden''
  have hmul :
      ((Fm : ℝ) + eta * (am : ℝ)) *
        (((Fm : ℝ) + eta * (am : ℝ))⁻¹) = 1 := by
    exact mul_inv_cancel₀ hdenD
  ring_nf at hmul ⊢
  nlinarith [hmul]

lemma
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_small_diff
    {Fm am : ℕ} (hFm : 0 < Fm) {eta : ℝ}
    (hden :
      conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor
        Fm am eta ≠ 0) :
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_uniformMass Fm -
        conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_smallMass Fm am eta =
      (am : ℝ) * eta /
        ((Fm : ℝ) *
          conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor
            Fm am eta) := by
  have hFne : (Fm : ℝ) ≠ 0 := by exact_mod_cast hFm.ne'
  have hden' : (Fm : ℝ) + (am : ℝ) * eta ≠ 0 := by
    simpa [conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor] using hden
  have hden'' : eta * (am : ℝ) + (Fm : ℝ) ≠ 0 := by
    simpa [add_comm, mul_comm, mul_left_comm] using hden'
  unfold conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_smallMass
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_uniformMass
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor
  field_simp [hFne, hden', hden'']
  ring_nf

/-- Paper label: `thm:conclusion-serrin-wulff-ray-affine-pressure-escort-uniformization`.

The finite part records the Euclidean two-level fiber law and the exact escort-TV formula.
The limiting part is the affine pressure transfer from the two exponential rates:
the common small-fiber power and the extracted layer factor. -/
theorem paper_conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization
    (s : ℝ) (smallPow layer S : ℕ → ℝ)
    (hlog :
      ∀ m,
        conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_pressureTerm S m =
          conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_pressureTerm
            smallPow m +
          conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_pressureTerm
            layer m)
    (hsmall :
      Tendsto
        (fun m =>
          conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_pressureTerm
            smallPow m)
        atTop (𝓝 (s * Real.log 2 - s * Real.log Real.goldenRatio)))
    (hlayer :
      Tendsto
        (fun m =>
          conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_pressureTerm layer m)
        atTop (𝓝 (Real.log Real.goldenRatio)))
    (Fm am : ℕ) (smallPow_m eta : ℝ) (hFm : 0 < Fm) (ham : am ≤ Fm)
    (heta : 0 ≤ eta)
    (hden_pos :
      0 <
        conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor
          Fm am eta) :
    Tendsto
        (fun m =>
          conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_pressureTerm S m)
        atTop (𝓝 (s * Real.log 2 + (1 - s) * Real.log Real.goldenRatio)) ∧
      conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_powerSum
          Fm am smallPow_m eta =
        smallPow_m *
          conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor
            Fm am eta ∧
      conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_twoLevelTV Fm am eta =
        conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_tvFormula
          Fm am eta := by
  have htarget :
      (s * Real.log 2 - s * Real.log Real.goldenRatio) + Real.log Real.goldenRatio =
        s * Real.log 2 + (1 - s) * Real.log Real.goldenRatio := by
    ring
  have hpressure :
      Tendsto
        (fun m =>
          conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_pressureTerm S m)
        atTop (𝓝 (s * Real.log 2 + (1 - s) * Real.log Real.goldenRatio)) := by
    simpa [hlog, htarget] using hsmall.add hlayer
  refine ⟨hpressure,
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_powerSum_factor
      ham smallPow_m eta,
    ?_⟩
  have hden_ne :
      conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor Fm am eta ≠
        0 := hden_pos.ne'
  have hlarge :=
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_large_diff
      hFm hden_ne
  have hsmalldiff :=
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_small_diff
      hFm hden_ne
  have hF_nonneg : 0 ≤ ((Fm : ℝ) - (am : ℝ)) := by
    exact sub_nonneg.mpr (by exact_mod_cast ham)
  have hden_nonneg :
      0 ≤
        (Fm : ℝ) *
          conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor
            Fm am eta := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le Fm) hden_pos.le
  have hlarge_nonneg :
      0 ≤
        conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_largeMass
            Fm am eta -
          conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_uniformMass Fm := by
    rw [hlarge]
    exact div_nonneg (mul_nonneg heta hF_nonneg) hden_nonneg
  have hsmall_nonneg :
      0 ≤
        conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_uniformMass Fm -
          conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_smallMass
            Fm am eta := by
    rw [hsmalldiff]
    exact div_nonneg (mul_nonneg (by positivity : 0 ≤ (am : ℝ)) heta) hden_nonneg
  have hsmall_nonpos :
      conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_smallMass
          Fm am eta -
        conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_uniformMass Fm ≤ 0 := by
    linarith
  unfold conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_twoLevelTV
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_tvFormula
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor
  rw [abs_of_nonneg hlarge_nonneg, abs_of_nonpos hsmall_nonpos]
  rw [Nat.cast_sub ham]
  unfold conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_largeMass
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_smallMass
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_uniformMass
    conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor
  have hFne : (Fm : ℝ) ≠ 0 := by exact_mod_cast hFm.ne'
  have hden_ne' : (Fm : ℝ) + (am : ℝ) * eta ≠ 0 := by
    simpa [conclusion_serrin_wulff_ray_affine_pressure_escort_uniformization_layerFactor] using
      hden_ne
  have hden_ne'' : eta * (am : ℝ) + (Fm : ℝ) ≠ 0 := by
    simpa [add_comm, mul_comm, mul_left_comm] using hden_ne'
  field_simp [hFne, hden_ne', hden_ne'']
  ring_nf

end

end Omega.Conclusion
