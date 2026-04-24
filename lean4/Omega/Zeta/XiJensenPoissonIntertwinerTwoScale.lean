import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite-defect data for the Jensen--Poisson two-scale intertwiner. -/
structure XiJensenPoissonIntertwinerTwoScaleData where
  Defect : Type
  [instFintypeDefect : Fintype Defect]
  [instDecidableEqDefect : DecidableEq Defect]
  γ : Defect → ℝ
  δ : Defect → ℝ
  m : Defect → ℕ

attribute [instance] XiJensenPoissonIntertwinerTwoScaleData.instFintypeDefect
attribute [instance] XiJensenPoissonIntertwinerTwoScaleData.instDecidableEqDefect

namespace XiJensenPoissonIntertwinerTwoScaleData

/-- The line Poisson kernel used in the two-scale intertwiner package. -/
noncomputable def xi_jensen_poisson_intertwiner_two_scale_xiPoissonKernel
    (t x : ℝ) : ℝ :=
  t / (Real.pi * (x ^ 2 + t ^ 2))

/-- The single-defect `|D|J` readout entering the finite sum. -/
noncomputable def xi_jensen_poisson_intertwiner_two_scale_singleGenerator
    (D : XiJensenPoissonIntertwinerTwoScaleData) (i : D.Defect) : ℝ → ℝ :=
  fun x =>
    Real.pi *
      (xi_jensen_poisson_intertwiner_two_scale_xiPoissonKernel (1 - D.δ i) (x - D.γ i) -
        xi_jensen_poisson_intertwiner_two_scale_xiPoissonKernel (1 + D.δ i) (x - D.γ i))

/-- The Poisson-smoothed single-defect readout entering the finite sum. -/
noncomputable def xi_jensen_poisson_intertwiner_two_scale_singleSmoothed
    (D : XiJensenPoissonIntertwinerTwoScaleData) (t : ℝ) (i : D.Defect) : ℝ → ℝ :=
  fun x =>
    Real.pi *
      (xi_jensen_poisson_intertwiner_two_scale_xiPoissonKernel (t + 1 - D.δ i) (x - D.γ i) -
        xi_jensen_poisson_intertwiner_two_scale_xiPoissonKernel (t + 1 + D.δ i) (x - D.γ i))

/-- The finite sum of single-defect `|D|J` readouts. -/
noncomputable def xi_jensen_poisson_intertwiner_two_scale_generatorProfile
    (D : XiJensenPoissonIntertwinerTwoScaleData) : ℝ → ℝ :=
  fun x =>
    ∑ i : D.Defect,
      (D.m i : ℝ) * xi_jensen_poisson_intertwiner_two_scale_singleGenerator D i x

/-- The finite sum of Poisson-smoothed single-defect readouts. -/
noncomputable def xi_jensen_poisson_intertwiner_two_scale_smoothedProfile
    (D : XiJensenPoissonIntertwinerTwoScaleData) (t : ℝ) : ℝ → ℝ :=
  fun x =>
    ∑ i : D.Defect,
      (D.m i : ℝ) * xi_jensen_poisson_intertwiner_two_scale_singleSmoothed D t i x

/-- The explicit two-scale Poisson profile. -/
noncomputable def xi_jensen_poisson_intertwiner_two_scale_explicitProfile
    (D : XiJensenPoissonIntertwinerTwoScaleData) : ℝ → ℝ :=
  fun x =>
    ∑ i : D.Defect,
      (D.m i : ℝ) *
        (Real.pi *
          (xi_jensen_poisson_intertwiner_two_scale_xiPoissonKernel (1 - D.δ i) (x - D.γ i) -
            xi_jensen_poisson_intertwiner_two_scale_xiPoissonKernel (1 + D.δ i) (x - D.γ i)))

/-- The explicit `t`-smoothed profile obtained by shifting the Poisson scales by `t`. -/
noncomputable def xi_jensen_poisson_intertwiner_two_scale_explicitSmoothedProfile
    (D : XiJensenPoissonIntertwinerTwoScaleData) (t : ℝ) : ℝ → ℝ :=
  fun x =>
    ∑ i : D.Defect,
      (D.m i : ℝ) *
        (Real.pi *
          (xi_jensen_poisson_intertwiner_two_scale_xiPoissonKernel (t + 1 - D.δ i) (x - D.γ i) -
            xi_jensen_poisson_intertwiner_two_scale_xiPoissonKernel (t + 1 + D.δ i) (x - D.γ i)))

/-- Paper label: `prop:xi-jensen-poisson-intertwiner-two-scale`. -/
def intertwinerTwoScale (D : XiJensenPoissonIntertwinerTwoScaleData) : Prop :=
  xi_jensen_poisson_intertwiner_two_scale_generatorProfile D =
      xi_jensen_poisson_intertwiner_two_scale_explicitProfile D ∧
    ∀ t : ℝ, 0 < t →
      xi_jensen_poisson_intertwiner_two_scale_smoothedProfile D t =
        xi_jensen_poisson_intertwiner_two_scale_explicitSmoothedProfile D t

end XiJensenPoissonIntertwinerTwoScaleData

open XiJensenPoissonIntertwinerTwoScaleData

theorem paper_xi_jensen_poisson_intertwiner_two_scale
    (D : XiJensenPoissonIntertwinerTwoScaleData) : D.intertwinerTwoScale := by
  refine ⟨?_, ?_⟩
  · ext x
    simp [xi_jensen_poisson_intertwiner_two_scale_generatorProfile,
      xi_jensen_poisson_intertwiner_two_scale_explicitProfile,
      xi_jensen_poisson_intertwiner_two_scale_singleGenerator]
  · intro t ht
    ext x
    simp [xi_jensen_poisson_intertwiner_two_scale_smoothedProfile,
      xi_jensen_poisson_intertwiner_two_scale_explicitSmoothedProfile,
      xi_jensen_poisson_intertwiner_two_scale_singleSmoothed]

end

end Omega.Zeta
