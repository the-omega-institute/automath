import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.LeyangBranchCoverSquareRoot
import Omega.UnitCirclePhaseArithmetic.LeyangLissajousSingularRingNormalForm

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `prop:leyang-lissajous-rotation-correspondence`. -/
theorem paper_leyang_lissajous_rotation_correspondence (θ φ : ℝ)
    (hcosθ : Real.cos θ ≠ 0) (hcosφ : Real.cos φ ≠ 0) (hcosθφ : Real.cos (θ + φ) ≠ 0) :
    leyangBranchCover θ = -(1 + Real.tan θ ^ 2) / 4 ∧
      leyangBranchCover (θ + φ) =
        ((1 + Real.tan φ ^ 2) * leyangBranchCover θ) / (1 - Real.tan θ * Real.tan φ) ^ 2 ∧
      (leyangBranchCover (θ + φ) + leyangBranchCover θ +
          4 * Real.sin φ ^ 2 * leyangBranchCover (θ + φ) * leyangBranchCover θ) ^ 2 =
        4 * Real.cos φ ^ 2 * leyangBranchCover (θ + φ) * leyangBranchCover θ ∧
      (Real.tan θ = Real.sqrt (-4 * leyangBranchCover θ - 1) →
        leyangBranchCover (θ + φ) =
          ((1 + Real.tan φ ^ 2) * leyangBranchCover θ) /
            (1 - Real.tan φ * Real.sqrt (-4 * leyangBranchCover θ - 1)) ^ 2) ∧
      (Real.tan θ = -Real.sqrt (-4 * leyangBranchCover θ - 1) →
        leyangBranchCover (θ + φ) =
          ((1 + Real.tan φ ^ 2) * leyangBranchCover θ) /
            (1 + Real.tan φ * Real.sqrt (-4 * leyangBranchCover θ - 1)) ^ 2) := by
  have hq : leyangBranchCover θ = -(1 + Real.tan θ ^ 2) / 4 := by
    unfold leyangBranchCover
    rw [← Real.inv_one_add_tan_sq hcosθ]
    have htan_ne : 1 + Real.tan θ ^ 2 ≠ 0 := by positivity
    field_simp [htan_ne]
  have hcos_add :
      Real.cos (θ + φ) = Real.cos θ * Real.cos φ * (1 - Real.tan θ * Real.tan φ) := by
    rw [Real.cos_add, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
    field_simp [hcosθ, hcosφ]
  have hden : 1 - Real.tan θ * Real.tan φ ≠ 0 := by
    intro hzero
    apply hcosθφ
    rw [hcos_add, hzero]
    ring
  have htan_add :
      Real.tan (θ + φ) = (Real.tan θ + Real.tan φ) / (1 - Real.tan θ * Real.tan φ) := by
    exact Real.tan_add'
      ⟨(Real.cos_ne_zero_iff.mp hcosθ), (Real.cos_ne_zero_iff.mp hcosφ)⟩
  have hp :
      leyangBranchCover (θ + φ) =
        ((1 + Real.tan φ ^ 2) * leyangBranchCover θ) / (1 - Real.tan θ * Real.tan φ) ^ 2 := by
    have hqθφ : leyangBranchCover (θ + φ) = -(1 + Real.tan (θ + φ) ^ 2) / 4 := by
      unfold leyangBranchCover
      rw [← Real.inv_one_add_tan_sq hcosθφ]
      have htan_ne : 1 + Real.tan (θ + φ) ^ 2 ≠ 0 := by positivity
      field_simp [htan_ne]
    calc
      leyangBranchCover (θ + φ)
          = -(1 + Real.tan (θ + φ) ^ 2) / 4 := hqθφ
      _ = -((1 + Real.tan φ ^ 2) * (1 + Real.tan θ ^ 2) / (1 - Real.tan θ * Real.tan φ) ^ 2) / 4 := by
            rw [htan_add]
            field_simp [hden]
            ring
      _ = ((1 + Real.tan φ ^ 2) * (-(1 + Real.tan θ ^ 2) / 4)) / (1 - Real.tan θ * Real.tan φ) ^ 2 := by
            field_simp [hden]
      _ = ((1 + Real.tan φ ^ 2) * leyangBranchCover θ) / (1 - Real.tan θ * Real.tan φ) ^ 2 := by
            rw [hq]
  have hcosθφ' : Real.cos ((((1 * 1 : ℕ) : ℝ) * θ) + ((1 : ℕ) : ℝ) * φ) ≠ 0 := by
    simpa using hcosθφ
  have hcosθ' : Real.cos (((1 * 1 : ℕ) : ℝ) * θ) ≠ 0 := by
    simpa using hcosθ
  have hcorr :
      (leyangBranchCover (θ + φ) + leyangBranchCover θ +
          4 * Real.sin φ ^ 2 * leyangBranchCover (θ + φ) * leyangBranchCover θ) ^ 2 =
        4 * Real.cos φ ^ 2 * leyangBranchCover (θ + φ) * leyangBranchCover θ := by
    simpa [leyangBranchCover] using
      paper_leyang_lissajous_singular_ring_normal_form 1 1 θ φ hcosθφ' hcosθ'
  refine ⟨hq, hp, hcorr, ?_, ?_⟩
  · intro hbranch
    rw [hp, hbranch]
    ring_nf
  · intro hbranch
    rw [hp, hbranch]
    ring_nf

end Omega.UnitCirclePhaseArithmetic
