import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- The polynomial `C(z) = 1 - (1 - p) z - p (1 - p) z²` from the compressed Bernoulli-`p`
large-deviation parametrization. -/
def bernoulliPLdpCompressedC (p z : ℝ) : ℝ :=
  1 - (1 - p) * z - p * (1 - p) * z ^ 2

/-- The compressed cubic obtained after eliminating `u = exp θ` from the pressure-cycle
equation. -/
def bernoulliPLdpCompressedCubicPolynomial (p z v : ℝ) : ℝ :=
  (1 - p) * v ^ 3 + p * z ^ 3 * bernoulliPLdpCompressedC p z * v -
    p * z ^ 3 * bernoulliPLdpCompressedC p z

/-- Concrete data for the Bernoulli-`p` compressed cubic LDP parametrization. The fields are the
physical parameters together with the pressure-cycle equation and the two nonvanishing
denominators needed for the closed forms. -/
structure BernoulliPLdpCompressedCubicData where
  p : ℝ
  θ : ℝ
  z : ℝ
  hp : 0 < p
  hp1 : p < 1
  hz : 0 < z
  cycleEquation :
    bernoulliPLdpCompressedC p z * (1 - p * Real.exp θ * z ^ 2) =
      p ^ 2 * (1 - p) * (Real.exp θ) ^ 3 * z ^ 3
  hOneSubK : 1 - (1 - p) * z ≠ 0
  hOneSubV : 1 - p * Real.exp θ * z ^ 2 ≠ 0

namespace BernoulliPLdpCompressedCubicData

/-- The cycle-tilt parameter `u = exp θ`. -/
noncomputable def u (D : BernoulliPLdpCompressedCubicData) : ℝ :=
  Real.exp D.θ

/-- The compressed dual variable `v = p u z²`. -/
noncomputable def v (D : BernoulliPLdpCompressedCubicData) : ℝ :=
  D.p * D.u * D.z ^ 2

/-- Closed form for `E_θ[K]`. -/
noncomputable def kMean (D : BernoulliPLdpCompressedCubicData) : ℝ :=
  ((1 - D.p) * D.z) / (1 - (1 - D.p) * D.z)

/-- Closed form for `E_θ[N]`. -/
noncomputable def nMean (D : BernoulliPLdpCompressedCubicData) : ℝ :=
  D.v / (1 - D.v)

/-- Closed form for `E_θ[M]`. -/
noncomputable def mMean (D : BernoulliPLdpCompressedCubicData) : ℝ :=
  bernoulliPLdpCompressedC D.p D.z / (D.p * (1 - D.p) * D.z ^ 2)

/-- Closed form for `E_θ[X₀]`. -/
noncomputable def xMean (D : BernoulliPLdpCompressedCubicData) : ℝ :=
  D.mMean * (3 + D.nMean)

/-- Closed form for `E_θ[L₀]`. -/
noncomputable def lMean (D : BernoulliPLdpCompressedCubicData) : ℝ :=
  2 + D.kMean + D.mMean * (D.kMean + 3 + 2 * D.nMean)

/-- The slope parameter `s(θ) = E_θ[X₀] / E_θ[L₀]`. -/
noncomputable def sValue (D : BernoulliPLdpCompressedCubicData) : ℝ :=
  D.xMean / D.lMean

/-- The Legendre quantity `I(θ) = θ s(θ) - P(θ)` with `z = exp (-P(θ))`. -/
noncomputable def rateValue (D : BernoulliPLdpCompressedCubicData) : ℝ :=
  D.θ * D.sValue + Real.log D.z

/-- The compressed cubic relation in the variables `(v, z)`. -/
def compressedCubic (D : BernoulliPLdpCompressedCubicData) : Prop :=
  bernoulliPLdpCompressedCubicPolynomial D.p D.z D.v = 0

/-- The rational parametrization of `s(θ)` coming from the closed forms of
`E_θ[M]`, `E_θ[K]`, and `E_θ[N]`. -/
def sParameterization (D : BernoulliPLdpCompressedCubicData) : Prop :=
  D.xMean = D.mMean * ((3 - 2 * D.v) / (1 - D.v)) ∧
    D.lMean = 2 + D.kMean + D.mMean * (D.kMean + (3 - D.v) / (1 - D.v)) ∧
    D.sValue =
      (D.mMean * ((3 - 2 * D.v) / (1 - D.v))) /
        (2 + D.kMean + D.mMean * (D.kMean + (3 - D.v) / (1 - D.v)))

/-- The logarithmic parametrization of the rate function. -/
def rateParameterization (D : BernoulliPLdpCompressedCubicData) : Prop :=
  D.rateValue = D.sValue * Real.log (D.v / (D.p * D.z ^ 2)) + Real.log D.z

end BernoulliPLdpCompressedCubicData

/-- Paper-facing package for the Bernoulli-`p` compressed cubic LDP parametrization.
    thm:fold-bernoulli-p-ldp-compressed-cubic-parametrization -/
theorem paper_fold_bernoulli_p_ldp_compressed_cubic_parametrization
    (D : BernoulliPLdpCompressedCubicData) :
    D.compressedCubic ∧ D.sParameterization ∧ D.rateParameterization := by
  have hp_ne : D.p ≠ 0 := ne_of_gt D.hp
  have hz_ne : D.z ≠ 0 := ne_of_gt D.hz
  have hz2_ne : D.z ^ 2 ≠ 0 := pow_ne_zero 2 hz_ne
  have hOneSubV : 1 - D.v ≠ 0 := by
    simpa [BernoulliPLdpCompressedCubicData.v, BernoulliPLdpCompressedCubicData.u] using D.hOneSubV
  have hScaled := congrArg (fun x : ℝ => D.p * D.z ^ 3 * x) D.cycleEquation
  have hCubic : D.compressedCubic := by
    have hScaledEq := hScaled
    unfold BernoulliPLdpCompressedCubicData.compressedCubic
      bernoulliPLdpCompressedCubicPolynomial
    simp [BernoulliPLdpCompressedCubicData.v, BernoulliPLdpCompressedCubicData.u] at hScaledEq ⊢
    ring_nf at hScaledEq
    nlinarith [hScaledEq]
  have hXClosed :
      D.xMean = D.mMean * ((3 - 2 * D.v) / (1 - D.v)) := by
    have hFrac : 3 + D.nMean = (3 - 2 * D.v) / (1 - D.v) := by
      unfold BernoulliPLdpCompressedCubicData.nMean
      field_simp [hOneSubV]
      ring
    unfold BernoulliPLdpCompressedCubicData.xMean
    rw [hFrac]
  have hLClosed :
      D.lMean = 2 + D.kMean + D.mMean * (D.kMean + (3 - D.v) / (1 - D.v)) := by
    have hFrac : D.kMean + 3 + 2 * D.nMean = D.kMean + (3 - D.v) / (1 - D.v) := by
      unfold BernoulliPLdpCompressedCubicData.nMean
      field_simp [hOneSubV]
      ring
    unfold BernoulliPLdpCompressedCubicData.lMean
    rw [hFrac]
  have hS : D.sParameterization := by
    refine ⟨hXClosed, hLClosed, ?_⟩
    unfold BernoulliPLdpCompressedCubicData.sValue
    rw [hXClosed, hLClosed]
  have hQuot : D.v / (D.p * D.z ^ 2) = Real.exp D.θ := by
    unfold BernoulliPLdpCompressedCubicData.v BernoulliPLdpCompressedCubicData.u
    field_simp [hp_ne, hz2_ne]
  have hRate : D.rateParameterization := by
    unfold BernoulliPLdpCompressedCubicData.rateParameterization
      BernoulliPLdpCompressedCubicData.rateValue
    rw [hQuot, Real.log_exp]
    ring
  exact ⟨hCubic, hS, hRate⟩

end Omega.Folding
