import Mathlib

open Filter Set

namespace Omega.Conclusion

noncomputable section

/-- The angle variable `x_k = π / (4k + 2)`. -/
def conclusion_lk_first_zero_monotone_approach_x (k : ℕ) : ℝ :=
  Real.pi / ((4 * k + 2 : ℕ) : ℝ)

/-- The first-zero scaling constant written as `(π² / 4) * sinc(x_k)^2`. -/
def conclusion_lk_first_zero_monotone_approach_alpha (k : ℕ) : ℝ :=
  (Real.pi ^ 2 / 4) * Real.sinc (conclusion_lk_first_zero_monotone_approach_x k) ^ 2

/-- The equivalent rescaled largest-eigenvalue expression `1 / (4 α_k)`. -/
def conclusion_lk_first_zero_monotone_approach_eigenRatio (k : ℕ) : ℝ :=
  1 / (4 * conclusion_lk_first_zero_monotone_approach_alpha k)

lemma conclusion_lk_first_zero_monotone_approach_x_pos (k : ℕ) :
    0 < conclusion_lk_first_zero_monotone_approach_x k := by
  unfold conclusion_lk_first_zero_monotone_approach_x
  exact div_pos Real.pi_pos (by positivity)

lemma conclusion_lk_first_zero_monotone_approach_x_lt_pi (k : ℕ) :
    conclusion_lk_first_zero_monotone_approach_x k < Real.pi := by
  unfold conclusion_lk_first_zero_monotone_approach_x
  have hdenNat : 1 < 4 * k + 2 := by omega
  have hden : (1 : ℝ) < ((4 * k + 2 : ℕ) : ℝ) := by exact_mod_cast hdenNat
  have hpi : Real.pi / ((4 * k + 2 : ℕ) : ℝ) < Real.pi / 1 := by
    exact (div_lt_div_iff_of_pos_left Real.pi_pos (by positivity) (by positivity)).2 hden
  simpa using hpi

lemma conclusion_lk_first_zero_monotone_approach_x_mem_Icc (k : ℕ) :
    conclusion_lk_first_zero_monotone_approach_x k ∈ Set.Icc 0 Real.pi := by
  exact ⟨(conclusion_lk_first_zero_monotone_approach_x_pos k).le,
    (conclusion_lk_first_zero_monotone_approach_x_lt_pi k).le⟩

lemma conclusion_lk_first_zero_monotone_approach_x_ne_zero (k : ℕ) :
    conclusion_lk_first_zero_monotone_approach_x k ≠ 0 := by
  exact (conclusion_lk_first_zero_monotone_approach_x_pos k).ne'

lemma conclusion_lk_first_zero_monotone_approach_sinc_pos (k : ℕ) :
    0 < Real.sinc (conclusion_lk_first_zero_monotone_approach_x k) := by
  rw [Real.sinc_of_ne_zero (conclusion_lk_first_zero_monotone_approach_x_ne_zero k)]
  exact div_pos
    (Real.sin_pos_of_pos_of_lt_pi
      (conclusion_lk_first_zero_monotone_approach_x_pos k)
      (conclusion_lk_first_zero_monotone_approach_x_lt_pi k))
    (conclusion_lk_first_zero_monotone_approach_x_pos k)

lemma conclusion_lk_first_zero_monotone_approach_x_strictAnti :
    StrictAnti conclusion_lk_first_zero_monotone_approach_x := by
  intro k l hkl
  unfold conclusion_lk_first_zero_monotone_approach_x
  have hk0 : (0 : ℝ) < ((4 * k + 2 : ℕ) : ℝ) := by positivity
  have hden : (((4 * k + 2 : ℕ) : ℝ)) < (((4 * l + 2 : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 4 * k + 2 < 4 * l + 2)
  have hInv :
      (1 : ℝ) / (((4 * l + 2 : ℕ) : ℝ)) < 1 / (((4 * k + 2 : ℕ) : ℝ)) :=
    one_div_lt_one_div_of_lt hk0 hden
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    mul_lt_mul_of_pos_left hInv Real.pi_pos

lemma conclusion_lk_first_zero_monotone_approach_alpha_pos (k : ℕ) :
    0 < conclusion_lk_first_zero_monotone_approach_alpha k := by
  unfold conclusion_lk_first_zero_monotone_approach_alpha
  have hconst : 0 < Real.pi ^ 2 / 4 := by positivity
  have hsinc : 0 < Real.sinc (conclusion_lk_first_zero_monotone_approach_x k) := by
    exact conclusion_lk_first_zero_monotone_approach_sinc_pos k
  exact mul_pos hconst (pow_pos hsinc 2)

/-- Paper label: `cor:conclusion-Lk-first-zero-monotone-approach`.

The sequence `α_k = (π² / 4) * sinc(x_k)^2` with `x_k = π / (4k + 2)` is strictly increasing
because `sin x / x` is strictly decreasing on `(0, π)`, and it converges to `π² / 4` by
continuity of `sinc` at the origin. The equivalent eigenvalue ratio is `1 / (4 α_k)`. -/
theorem paper_conclusion_lk_first_zero_monotone_approach :
    StrictMono conclusion_lk_first_zero_monotone_approach_alpha ∧
    Tendsto conclusion_lk_first_zero_monotone_approach_alpha atTop (nhds (Real.pi ^ 2 / 4)) ∧
    StrictAnti conclusion_lk_first_zero_monotone_approach_eigenRatio ∧
    Tendsto conclusion_lk_first_zero_monotone_approach_eigenRatio atTop (nhds (1 / Real.pi ^ 2)) := by
  have halpha_strict : StrictMono conclusion_lk_first_zero_monotone_approach_alpha := by
    intro k l hkl
    have hx :
        conclusion_lk_first_zero_monotone_approach_x l <
          conclusion_lk_first_zero_monotone_approach_x k :=
      conclusion_lk_first_zero_monotone_approach_x_strictAnti hkl
    have hsinc :
        Real.sinc (conclusion_lk_first_zero_monotone_approach_x k) <
          Real.sinc (conclusion_lk_first_zero_monotone_approach_x l) := by
      rw [Real.sinc_of_ne_zero (conclusion_lk_first_zero_monotone_approach_x_ne_zero k),
        Real.sinc_of_ne_zero (conclusion_lk_first_zero_monotone_approach_x_ne_zero l)]
      simpa using
        strictConcaveOn_sin_Icc.secant_strict_mono
          (a := 0)
          (x := conclusion_lk_first_zero_monotone_approach_x l)
          (y := conclusion_lk_first_zero_monotone_approach_x k)
          (by simp [Real.pi_pos.le])
          (conclusion_lk_first_zero_monotone_approach_x_mem_Icc l)
          (conclusion_lk_first_zero_monotone_approach_x_mem_Icc k)
          (conclusion_lk_first_zero_monotone_approach_x_ne_zero l)
          (conclusion_lk_first_zero_monotone_approach_x_ne_zero k)
          hx
    have hsquare :
        Real.sinc (conclusion_lk_first_zero_monotone_approach_x k) ^ 2 <
          Real.sinc (conclusion_lk_first_zero_monotone_approach_x l) ^ 2 := by
      have hkpos := conclusion_lk_first_zero_monotone_approach_sinc_pos k
      have hlpos := conclusion_lk_first_zero_monotone_approach_sinc_pos l
      nlinarith
    unfold conclusion_lk_first_zero_monotone_approach_alpha
    exact mul_lt_mul_of_pos_left hsquare (by positivity)
  have hx_zero :
      Tendsto conclusion_lk_first_zero_monotone_approach_x atTop (nhds 0) := by
    have hzero :
        Tendsto (fun k : ℕ => (1 : ℝ) / (((4 * k + 2 : ℕ) : ℝ))) atTop (nhds 0) := by
      change Tendsto (((fun m : ℕ => (1 : ℝ) / (m : ℝ)) ∘ fun k : ℕ => 4 * k + 2)) atTop (nhds 0)
      have hshift : Tendsto (fun k : ℕ => 4 * k + 2) atTop atTop := by
        refine tendsto_atTop.2 ?_
        intro b
        filter_upwards [eventually_ge_atTop b] with k hk
        omega
      exact (tendsto_const_div_atTop_nhds_zero_nat 1).comp hshift
    have hEq :
        conclusion_lk_first_zero_monotone_approach_x =
          fun k : ℕ => Real.pi * ((1 : ℝ) / (((4 * k + 2 : ℕ) : ℝ))) := by
      funext k
      simp [conclusion_lk_first_zero_monotone_approach_x, div_eq_mul_inv, mul_assoc, mul_comm,
        mul_left_comm]
    rw [hEq]
    simpa using (tendsto_const_nhds.mul hzero)
  have hsinc_tendsto :
      Tendsto (fun k : ℕ => Real.sinc (conclusion_lk_first_zero_monotone_approach_x k))
        atTop (nhds 1) := by
    simpa using Real.continuous_sinc.continuousAt.tendsto.comp hx_zero
  have halpha_tendsto :
      Tendsto conclusion_lk_first_zero_monotone_approach_alpha atTop (nhds (Real.pi ^ 2 / 4)) := by
    have hsquare :
        Tendsto
          (fun k : ℕ => Real.sinc (conclusion_lk_first_zero_monotone_approach_x k) ^ 2)
          atTop (nhds (1 ^ 2)) := hsinc_tendsto.pow 2
    simpa [conclusion_lk_first_zero_monotone_approach_alpha] using
      (tendsto_const_nhds.mul hsquare)
  have heigen_strict : StrictAnti conclusion_lk_first_zero_monotone_approach_eigenRatio := by
    intro k l hkl
    have halpha :
        conclusion_lk_first_zero_monotone_approach_alpha k <
          conclusion_lk_first_zero_monotone_approach_alpha l :=
      halpha_strict hkl
    have hden :
        4 * conclusion_lk_first_zero_monotone_approach_alpha k <
          4 * conclusion_lk_first_zero_monotone_approach_alpha l := by
      nlinarith
    have hkpos : 0 < 4 * conclusion_lk_first_zero_monotone_approach_alpha k := by
      exact mul_pos (by positivity) (conclusion_lk_first_zero_monotone_approach_alpha_pos k)
    simpa [conclusion_lk_first_zero_monotone_approach_eigenRatio] using
      one_div_lt_one_div_of_lt hkpos hden
  have heigen_tendsto :
      Tendsto conclusion_lk_first_zero_monotone_approach_eigenRatio atTop
        (nhds (1 / Real.pi ^ 2)) := by
    have hAlphaInv :
        Tendsto
          (fun k : ℕ => (conclusion_lk_first_zero_monotone_approach_alpha k)⁻¹)
          atTop
          (nhds ((Real.pi ^ 2 / 4)⁻¹)) := by
      have hAlphaNe : (Real.pi ^ 2 / 4 : ℝ) ≠ 0 := by positivity
      exact (ContinuousAt.inv₀ continuousAt_id hAlphaNe).tendsto.comp halpha_tendsto
    have hmul :
        Tendsto
          (fun k : ℕ =>
            (conclusion_lk_first_zero_monotone_approach_alpha k)⁻¹ * (4 : ℝ)⁻¹)
          atTop (nhds (((Real.pi ^ 2 / 4)⁻¹) * (4 : ℝ)⁻¹)) := by
      exact hAlphaInv.mul tendsto_const_nhds
    have hEq :
        conclusion_lk_first_zero_monotone_approach_eigenRatio =
          fun k : ℕ =>
            (conclusion_lk_first_zero_monotone_approach_alpha k)⁻¹ * (4 : ℝ)⁻¹ := by
      funext k
      simp [conclusion_lk_first_zero_monotone_approach_eigenRatio, one_div, mul_assoc, mul_comm]
    rw [hEq]
    have hconst : ((4 / Real.pi ^ 2 : ℝ) * (4 : ℝ)⁻¹) = (Real.pi ^ 2)⁻¹ := by
      field_simp [show (Real.pi ^ 2 : ℝ) ≠ 0 by positivity]
    simpa [hconst, one_div] using hmul
  exact ⟨halpha_strict, halpha_tendsto, heigen_strict, heigen_tendsto⟩

end

end Omega.Conclusion
