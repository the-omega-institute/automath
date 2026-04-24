import Mathlib
import Mathlib.MeasureTheory.Measure.Dirac

namespace Omega.Zeta

open Filter MeasureTheory

/-- Paper label: `thm:xi-poisson-cauchy-mixture-t4-optimality-rigidity`. A `t^-4` Poisson--Cauchy
KL asymptotic rigidifies the centered mixture: if the scaled KL term tends to `σ^4 / 8`, then
`o(t^-4)` is equivalent to vanishing second moment, and vanishing second moment forces the mixing
measure to be `δ₀`; in that rigid case the two channels coincide and the KL term vanishes
identically. -/
theorem paper_xi_poisson_cauchy_mixture_t4_optimality_rigidity
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (σ : ℝ) (p q Dkl : ℝ → ℝ)
    (hMoment : Integrable (fun y : ℝ => y ^ 2) μ)
    (hSigma : σ ^ 2 = ∫ y, y ^ 2 ∂μ)
    (hAsymp : Tendsto (fun t : ℝ => t ^ 4 * Dkl t) atTop (nhds (σ ^ 4 / 8)))
    (hDiracEq : μ = Measure.dirac 0 → ∀ t > 0, p t = q t)
    (hKlZero : (∀ t > 0, p t = q t) → ∀ t > 0, Dkl t = 0) :
    (Tendsto (fun t : ℝ => t ^ 4 * Dkl t) atTop (nhds 0) ↔ σ ^ 2 = 0) ∧
      (σ ^ 2 = 0 ↔ μ = Measure.dirac 0 ∧ ∀ t > 0, p t = q t) := by
  have hsigma_dirac : σ ^ 2 = 0 ↔ μ = Measure.dirac 0 := by
    constructor
    · intro hσ0
      have hint0 : ∫ y, y ^ 2 ∂μ = 0 := by
        rw [← hSigma]
        exact hσ0
      have hsq_ae : (fun y : ℝ => y ^ 2) =ᵐ[μ] 0 := by
        exact (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg y) hMoment).1 hint0
      have hid_ae : (fun y : ℝ => y) =ᵐ[μ] fun _ => 0 := by
        filter_upwards [hsq_ae] with y hy
        exact sq_eq_zero_iff.mp hy
      calc
        μ = μ.map id := by rw [Measure.map_id]
        _ = μ.map (fun _ : ℝ => 0) := Measure.map_congr hid_ae
        _ = (μ Set.univ) • Measure.dirac 0 := Measure.map_const μ 0
        _ = Measure.dirac 0 := by simp
    · intro hμ
      rw [hμ] at hSigma
      simpa using hSigma
  constructor
  · constructor
    · intro hLittleO
      have hlim_eq : σ ^ 4 / 8 = 0 := by
        exact tendsto_nhds_unique hAsymp hLittleO
      nlinarith
    · intro hσ0
      have hEq : ∀ t > 0, p t = q t := hDiracEq ((hsigma_dirac).1 hσ0)
      have hzero : ∀ t > 0, Dkl t = 0 := hKlZero hEq
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      simp [hzero t ht]
  · constructor
    · intro hσ0
      refine ⟨(hsigma_dirac).1 hσ0, hDiracEq ((hsigma_dirac).1 hσ0)⟩
    · rintro ⟨hμ, _⟩
      exact (hsigma_dirac).2 hμ

end Omega.Zeta
