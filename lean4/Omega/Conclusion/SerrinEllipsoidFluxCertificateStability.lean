import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The conclusion-level ellipsoid flux decoder `Q = (n / B₀) B` in the scalar seed model. -/
noncomputable def serrinEllipsoidFluxDecode (n : ℕ) (B0 B : ℝ) : ℝ :=
  (n : ℝ) / B0 * B

/-- Scalar specialization of the ellipsoid-flux stability estimate from the conclusion section.
`prop:conclusion-serrin-ellipsoid-flux-certificate-stability` -/
theorem paper_conclusion_serrin_ellipsoid_flux_certificate_stability
    (n : ℕ) {B0 δ0 B Δ : ℝ} (hB0 : 0 < B0) (hδ0 : |δ0| < B0) :
    let QΩ := serrinEllipsoidFluxDecode n B0 B
    let Qtilde := serrinEllipsoidFluxDecode n (B0 + δ0) (B + Δ)
    |Qtilde - QΩ| ≤
      (n : ℝ) / (B0 - |δ0|) * |Δ| + |δ0| / (B0 - |δ0|) * |QΩ| := by
  dsimp [serrinEllipsoidFluxDecode]
  have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hgap : 0 < B0 - |δ0| := by linarith
  have hden : 0 < B0 + δ0 := by
    have hneg : -|δ0| ≤ δ0 := by simpa using neg_abs_le δ0
    linarith
  have hB0_ne : B0 ≠ 0 := ne_of_gt hB0
  have hden_ne : B0 + δ0 ≠ 0 := ne_of_gt hden
  have hδ_le : B0 - |δ0| ≤ B0 + δ0 := by
    have hneg : -|δ0| ≤ δ0 := by simpa using neg_abs_le δ0
    linarith
  have hdecomp :
      (n : ℝ) / (B0 + δ0) * (B + Δ) - (n : ℝ) / B0 * B =
        (n : ℝ) / (B0 + δ0) * Δ - (δ0 / (B0 + δ0)) * ((n : ℝ) / B0 * B) := by
    field_simp [hB0_ne, hden_ne]
    ring
  have hcoefΔ :
      |(n : ℝ) / (B0 + δ0)| ≤ (n : ℝ) / (B0 - |δ0|) := by
    have hdiv :
        (n : ℝ) / (B0 + δ0) ≤ (n : ℝ) / (B0 - |δ0|) :=
      div_le_div_of_nonneg_left hn hgap hδ_le
    simpa [abs_of_nonneg (div_nonneg hn hden.le)] using hdiv
  have hcoefQ :
      |δ0 / (B0 + δ0)| ≤ |δ0| / (B0 - |δ0|) := by
    have hdiv :
        |δ0| / (B0 + δ0) ≤ |δ0| / (B0 - |δ0|) :=
      div_le_div_of_nonneg_left (abs_nonneg δ0) hgap hδ_le
    simpa [abs_div, abs_of_nonneg hden.le] using hdiv
  have htriangle :
      |(n : ℝ) / (B0 + δ0) * Δ - (δ0 / (B0 + δ0)) * ((n : ℝ) / B0 * B)| ≤
        |(n : ℝ) / (B0 + δ0) * Δ| + |(δ0 / (B0 + δ0)) * ((n : ℝ) / B0 * B)| := by
    rw [abs_sub_le_iff]
    constructor <;>
      linarith [neg_abs_le ((n : ℝ) / (B0 + δ0) * Δ), le_abs_self ((n : ℝ) / (B0 + δ0) * Δ),
        neg_abs_le ((δ0 / (B0 + δ0)) * ((n : ℝ) / B0 * B)),
        le_abs_self ((δ0 / (B0 + δ0)) * ((n : ℝ) / B0 * B))]
  calc
    |(n : ℝ) / (B0 + δ0) * (B + Δ) - (n : ℝ) / B0 * B|
      = |(n : ℝ) / (B0 + δ0) * Δ - (δ0 / (B0 + δ0)) * ((n : ℝ) / B0 * B)| := by
          rw [hdecomp]
    _ ≤ |(n : ℝ) / (B0 + δ0) * Δ| + |(δ0 / (B0 + δ0)) * ((n : ℝ) / B0 * B)| := htriangle
    _ = |(n : ℝ) / (B0 + δ0)| * |Δ| +
          |δ0 / (B0 + δ0)| * |(n : ℝ) / B0 * B| := by
          rw [abs_mul, abs_mul]
    _ ≤ (n : ℝ) / (B0 - |δ0|) * |Δ| +
          |δ0| / (B0 - |δ0|) * |(n : ℝ) / B0 * B| := by
          gcongr

end Omega.Conclusion
