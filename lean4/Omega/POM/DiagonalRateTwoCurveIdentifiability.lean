import Omega.POM.DiagonalRateRateCurveIdentifiability

namespace Omega.POM

/-- The scalar-collapse package underlying the two-curve identifiability corollary. -/
def pom_diagonal_rate_two_curve_identifiability_data
    {State : Type} [Fintype State] [DecidableEq State]
    (w : State → ℝ) (hw_pos : ∀ x, 0 < w x) (hw_sum : ∑ x, w x = 1) (κ : ℝ) (hκ : 0 < κ)
    (A : ℝ) (hA_pos : 0 < A) (hA_lt_one : A < 1)
    (gapStrictMono :
      StrictMono fun t : ℝ =>
        t - ∑ x, (Real.sqrt (t ^ 2 + 4 * κ * w x) - t) / (2 * κ))
    (hA_fixed : A = ∑ x, (Real.sqrt (A ^ 2 + 4 * κ * w x) - A) / (2 * κ))
    (hdelta0_pos : 0 < 1 - ∑ x, (w x) ^ 2) :
    DiagonalRateScalarCollapseData :=
  { State := State
    instFintype := inferInstance
    instDecidableEq := inferInstance
    w := w
    hw_pos := hw_pos
    hw_sum := hw_sum
    κ := κ
    hκ := hκ
    A := A
    hA_pos := hA_pos
    hA_lt_one := hA_lt_one
    gapStrictMono := gapStrictMono
    hA_fixed := hA_fixed
    hdelta0_pos := hdelta0_pos }

/-- Paper label: `cor:pom-diagonal-rate-two-curve-identifiability`. The second observed curve is
packaged as another value of the already formalized scalar-collapse distortion map; the existing
one-curve identifiability theorem then forces the two parameters to coincide. -/
theorem paper_pom_diagonal_rate_two_curve_identifiability
    {State : Type} [Fintype State] [DecidableEq State]
    (w : State → ℝ) (hw_pos : ∀ x, 0 < w x) (hw_sum : ∑ x, w x = 1) (κ : ℝ) (hκ : 0 < κ)
    (A : ℝ) (hA_pos : 0 < A) (hA_lt_one : A < 1)
    (gapStrictMono :
      StrictMono fun t : ℝ =>
        t - ∑ x, (Real.sqrt (t ^ 2 + 4 * κ * w x) - t) / (2 * κ))
    (hA_fixed : A = ∑ x, (Real.sqrt (A ^ 2 + 4 * κ * w x) - A) / (2 * κ))
    (hdelta0_pos : 0 < 1 - ∑ x, (w x) ^ 2)
    (κ₂ : ℝ) (hκ₂ : 0 < κ₂)
    (hcurve₂ :
      (pom_diagonal_rate_two_curve_identifiability_data w hw_pos hw_sum κ hκ A hA_pos hA_lt_one
        gapStrictMono hA_fixed hdelta0_pos).distortionMap κ₂ =
      (pom_diagonal_rate_two_curve_identifiability_data w hw_pos hw_sum κ hκ A hA_pos hA_lt_one
        gapStrictMono hA_fixed hdelta0_pos).distortionMap κ) :
    pom_diagonal_rate_rate_curve_identifiability_statement w hw_pos hw_sum κ hκ A hA_pos
      hA_lt_one gapStrictMono hA_fixed hdelta0_pos ∧
      κ₂ = κ := by
  let D :=
    pom_diagonal_rate_two_curve_identifiability_data w hw_pos hw_sum κ hκ A hA_pos hA_lt_one
      gapStrictMono hA_fixed hdelta0_pos
  have hbase :=
    paper_pom_diagonal_rate_rate_curve_identifiability w hw_pos hw_sum κ hκ A hA_pos hA_lt_one
      gapStrictMono hA_fixed hdelta0_pos
  rcases hbase with ⟨hfixed, hdist, huniq, hweights⟩
  have hκ_mem : κ ∈ Set.Ioi 0 ∧ D.distortionMap κ = D.distortionMap D.κ := by
    refine ⟨hκ, ?_⟩
    rfl
  have hκ₂_mem : κ₂ ∈ Set.Ioi 0 ∧ D.distortionMap κ₂ = D.distortionMap D.κ := by
    refine ⟨hκ₂, ?_⟩
    simpa [D] using hcurve₂
  rcases huniq with ⟨κ₀, hκ₀, huniq₀⟩
  have hκ_eq : κ = κ₀ := huniq₀ κ hκ_mem
  have hκ₂_eq : κ₂ = κ₀ := huniq₀ κ₂ hκ₂_mem
  refine ⟨⟨hfixed, hdist, ⟨κ₀, hκ₀, huniq₀⟩, hweights⟩, ?_⟩
  calc
    κ₂ = κ₀ := hκ₂_eq
    _ = κ := hκ_eq.symm

end Omega.POM
