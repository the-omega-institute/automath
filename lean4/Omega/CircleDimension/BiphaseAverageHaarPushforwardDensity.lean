import Mathlib

namespace Omega.CircleDimension

/-- The biphase change of variables `F(w, δ) = e^{iw} cos δ`. -/
noncomputable def biphaseAveragePoint (w δ : ℝ) : ℂ :=
  Complex.exp (w * Complex.I) * (Real.cos δ : ℂ)

/-- Radial law of `|F(U,V)|` after the `δ = (U - V) / 2` reduction. -/
noncomputable def biphaseRadialDensity (r : ℝ) : ℝ :=
  2 / (Real.pi * Real.sqrt (1 - r ^ 2))

/-- Planar density obtained from the radial law through `f_R(r) = 2π r ρ(r)`. -/
noncomputable def biphasePlanarDensity (r : ℝ) : ℝ :=
  1 / (Real.pi ^ 2 * r * Real.sqrt (1 - r ^ 2))

private theorem biphase_one_sub_sq_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 < 1 - r ^ 2 := by
  have hr2 : r ^ 2 < 1 := by
    nlinarith
  nlinarith

/-- Rotating both phases by the same angle multiplies the biphase average by the corresponding
global phase. -/
theorem biphaseAveragePoint_rotate (w φ δ : ℝ) :
    biphaseAveragePoint (w + φ) δ = Complex.exp (φ * Complex.I) * biphaseAveragePoint w δ := by
  unfold biphaseAveragePoint
  have hmul :
      (((w + φ : ℝ) : ℂ) * Complex.I) = Complex.I * (w : ℂ) + Complex.I * (φ : ℂ) := by
    calc
      (((w + φ : ℝ) : ℂ) * Complex.I) = (((w : ℂ) + (φ : ℂ)) * Complex.I) := by simp
      _ = Complex.I * (w : ℂ) + Complex.I * (φ : ℂ) := by ring
  rw [hmul, Complex.exp_add]
  ring_nf

private theorem biphase_radial_to_planar (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    biphaseRadialDensity r = 2 * Real.pi * r * biphasePlanarDensity r := by
  have hs : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.mpr (biphase_one_sub_sq_pos hr0 hr1)
  have hr : r ≠ 0 := hr0.ne'
  unfold biphaseRadialDensity biphasePlanarDensity
  field_simp [Real.pi_ne_zero, hr, hs.ne']

private theorem biphase_boundary_weighted (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Real.sqrt (1 - r ^ 2) * biphaseRadialDensity r = 2 / Real.pi := by
  have hs : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.mpr (biphase_one_sub_sq_pos hr0 hr1)
  unfold biphaseRadialDensity
  field_simp [Real.pi_ne_zero, hs.ne']

private theorem biphase_origin_weighted (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    r * biphasePlanarDensity r = 1 / (Real.pi ^ 2 * Real.sqrt (1 - r ^ 2)) := by
  have hs : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.mpr (biphase_one_sub_sq_pos hr0 hr1)
  have hr : r ≠ 0 := hr0.ne'
  unfold biphasePlanarDensity
  field_simp [Real.pi_ne_zero, hr, hs.ne']

set_option maxHeartbeats 400000 in
/-- Paper-facing package for the Haar pushforward density of the biphase average map.
    thm:cdim-biphase-average-haar-pushforward-density -/
theorem paper_cdim_biphase_average_haar_pushforward_density :
    (∀ w φ δ, biphaseAveragePoint (w + φ) δ = Complex.exp (φ * Complex.I) * biphaseAveragePoint w δ)
      ∧
      (∀ r, 0 < r → r < 1 →
        biphaseRadialDensity r = 2 / (Real.pi * Real.sqrt (1 - r ^ 2)) ∧
          biphaseRadialDensity r = 2 * Real.pi * r * biphasePlanarDensity r) ∧
      (∀ r, 0 < r → r < 1 →
        Real.sqrt (1 - r ^ 2) * biphaseRadialDensity r = 2 / Real.pi) ∧
      (∀ r, 0 < r → r < 1 →
        r * biphasePlanarDensity r = 1 / (Real.pi ^ 2 * Real.sqrt (1 - r ^ 2))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w φ δ
    exact biphaseAveragePoint_rotate w φ δ
  · intro r hr0 hr1
    exact ⟨rfl, biphase_radial_to_planar r hr0 hr1⟩
  · intro r hr0 hr1
    exact biphase_boundary_weighted r hr0 hr1
  · intro r hr0 hr1
    exact biphase_origin_weighted r hr0 hr1

end Omega.CircleDimension
