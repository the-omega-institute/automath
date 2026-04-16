import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open scoped goldenRatio

namespace Omega.Folding.MetallicParetoFrontier

/-- The continuous metallic parameter recovered from the Perron root `λ`. -/
noncomputable def metallicAOfLambda (lam : ℝ) : ℝ :=
  lam - lam⁻¹

/-- The compression objective written directly in the Perron parameter. -/
noncomputable def metallicCompressionObjective (lam : ℝ) : ℝ :=
  Real.log (1 + lam⁻¹ - lam⁻¹ ^ 2)

/-- The certificate objective written directly in the Perron parameter. -/
noncomputable def metallicCertificateObjective (lam : ℝ) : ℝ :=
  (lam - lam⁻¹) / Real.log lam

/-- Auxiliary bridge function for the sharp logarithmic lower bound
    `log x > 2 (x - 1) / (x + 1)` on `x > 1`. -/
noncomputable def metallicCompressionBridge (x : ℝ) : ℝ :=
  Real.log x - ((x - 1) / (x + 1)) * 2

lemma metallicCompressionBridge_continuousOn_Ici_one :
    ContinuousOn metallicCompressionBridge (Set.Ici 1) := by
  intro x hx
  have hx1 : 1 ≤ x := hx
  have hx0 : 0 < x := by linarith
  have hne : x + 1 ≠ 0 := by linarith
  have hlog : ContinuousAt Real.log x := Real.continuousAt_log (by linarith)
  have hquot : ContinuousAt (fun y : ℝ => (y - 1) / (y + 1)) x := by
    exact (((continuous_id.sub continuous_const).continuousAt).div
      ((continuous_id.add continuous_const).continuousAt) hne)
  simpa [metallicCompressionBridge] using
    (hlog.sub (hquot.mul continuousAt_const)).continuousWithinAt

lemma metallicCompressionBridge_deriv_pos {x : ℝ}
    (hx : x ∈ interior (Set.Ici 1)) :
    0 < deriv metallicCompressionBridge x := by
  have hx1 : 1 < x := by simpa [interior_Ici, Set.mem_Ioi] using hx
  have hx0 : 0 < x := by linarith
  have hne : x + 1 ≠ 0 := by linarith
  have hquot :
      HasDerivAt (fun y : ℝ => (y - 1) / (y + 1))
        (((x + 1) - (x - 1)) / (x + 1) ^ 2) x := by
    simpa using
      ((hasDerivAt_id x).sub_const 1).div ((hasDerivAt_id x).add_const 1) hne
  have hf :
      HasDerivAt metallicCompressionBridge
        (x⁻¹ - (((x + 1) - (x - 1)) / (x + 1) ^ 2) * 2) x := by
    simpa [metallicCompressionBridge] using
      (Real.hasDerivAt_log hx0.ne').sub (hquot.mul (hasDerivAt_const x (2 : ℝ)))
  have hderiv :
      deriv metallicCompressionBridge x = (x - 1) ^ 2 / (x * (x + 1) ^ 2) := by
    rw [hf.deriv]
    field_simp [hx0.ne', hne]
    ring
  rw [hderiv]
  have hnum : 0 < (x - 1) ^ 2 := by
    have hneq : x - 1 ≠ 0 := sub_ne_zero.mpr hx1.ne'
    exact sq_pos_iff.mpr hneq
  have hden : 0 < x * (x + 1) ^ 2 := by positivity
  exact div_pos hnum hden

lemma log_gt_two_mul_sub_div_add {x : ℝ} (hx : 1 < x) :
    2 * (x - 1) / (x + 1) < Real.log x := by
  have hmono :=
    strictMonoOn_of_deriv_pos (convex_Ici (1 : ℝ))
      metallicCompressionBridge_continuousOn_Ici_one
      (fun x hx => metallicCompressionBridge_deriv_pos hx)
  have hbridge :
      metallicCompressionBridge 1 < metallicCompressionBridge x := by
    exact hmono (by simp [Set.mem_Ici]) (show x ∈ Set.Ici 1 by exact le_of_lt hx) hx
  have h1 : metallicCompressionBridge 1 = 0 := by
    norm_num [metallicCompressionBridge]
  have hpos : 0 < metallicCompressionBridge x := by
    simpa [h1] using hbridge
  dsimp [metallicCompressionBridge] at hpos
  have h' : ((x - 1) / (x + 1)) * 2 < Real.log x := by linarith
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h'

lemma metallicCompressionInside_pos {lam : ℝ} (hlam : 1 ≤ lam) :
    0 < 1 + lam⁻¹ - lam⁻¹ ^ 2 := by
  have hlam0 : 0 < lam := by linarith
  have hrew : 1 + lam⁻¹ - lam⁻¹ ^ 2 = 1 + (lam - 1) / lam ^ 2 := by
    field_simp [hlam0.ne']
    ring
  rw [hrew]
  have hfrac : 0 ≤ (lam - 1) / lam ^ 2 := by
    have hnum : 0 ≤ lam - 1 := by linarith
    have hden : 0 < lam ^ 2 := by positivity
    exact div_nonneg hnum hden.le
  linarith

lemma metallicCertificateObjective_continuousOn :
    ContinuousOn metallicCertificateObjective (Set.Ioi 1) := by
  intro x hx
  have hx1 : 1 < x := hx
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  have hnum : ContinuousAt (fun y : ℝ => y - y⁻¹) x := by
    exact continuousAt_id.sub (continuousAt_inv₀ hx0.ne')
  simpa [metallicCertificateObjective] using
    (hnum.div (Real.continuousAt_log hx0.ne') hlog).continuousWithinAt

lemma metallicCertificateObjective_deriv_pos {x : ℝ}
    (hx : x ∈ interior (Set.Ioi 1)) :
    0 < deriv metallicCertificateObjective x := by
  have hx1 : 1 < x := by simpa [interior_Ioi, Set.mem_Ioi] using hx
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  have hnum : HasDerivAt (fun y : ℝ => y - y⁻¹) (1 + x⁻¹ ^ 2) x := by
    simpa using (hasDerivAt_id x).sub (hasDerivAt_inv hx0.ne')
  have hk :
      HasDerivAt metallicCertificateObjective
        (((1 + x⁻¹ ^ 2) * Real.log x - (x - x⁻¹) * x⁻¹) / (Real.log x) ^ 2) x := by
    simpa [metallicCertificateObjective] using
      hnum.div (Real.hasDerivAt_log hx0.ne') hlog
  have hderiv :
      deriv metallicCertificateObjective x =
        (((1 + x⁻¹ ^ 2) * Real.log x) - (1 - x⁻¹ ^ 2)) / (Real.log x) ^ 2 := by
    rw [hk.deriv]
    have hx0ne : x ≠ 0 := hx0.ne'
    field_simp [hx0ne]
  rw [hderiv]
  have hsqlog : 0 < (Real.log x) ^ 2 := by positivity
  apply div_pos ?_ hsqlog
  have hx2 : 1 < x ^ 2 := by nlinarith [hx1, hx0]
  have hbridge : 2 * (x ^ 2 - 1) / (x ^ 2 + 1) < Real.log (x ^ 2) :=
    log_gt_two_mul_sub_div_add hx2
  have hlog2 : Real.log (x ^ 2) = 2 * Real.log x := by
    simpa [Real.rpow_natCast] using (Real.log_rpow hx0 (2 : ℝ))
  rw [hlog2] at hbridge
  have hbridge' : 2 * ((x ^ 2 - 1) / (x ^ 2 + 1)) < 2 * Real.log x := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbridge
  have hmain : (x ^ 2 - 1) / (x ^ 2 + 1) < Real.log x := by
    nlinarith [hbridge']
  have hden2 : 0 < x ^ 2 + 1 := by positivity
  have hmul : x ^ 2 - 1 < Real.log x * (x ^ 2 + 1) := by
    exact (div_lt_iff₀ hden2).mp hmain
  have hx2pos : 0 < x ^ 2 := by positivity
  have hdiv : (x ^ 2 - 1) / x ^ 2 < (Real.log x * (x ^ 2 + 1)) / x ^ 2 := by
    exact div_lt_div_of_pos_right hmul hx2pos
  have htarget : 1 - x⁻¹ ^ 2 < (1 + x⁻¹ ^ 2) * Real.log x := by
    have hx0ne : x ≠ 0 := hx0.ne'
    have hleft : (x ^ 2 - 1) / x ^ 2 = 1 - x⁻¹ ^ 2 := by
      field_simp [hx0ne]
    have hright : (Real.log x * (x ^ 2 + 1)) / x ^ 2 = (1 + x⁻¹ ^ 2) * Real.log x := by
      field_simp [hx0ne]
    rw [hleft, hright] at hdiv
    exact hdiv
  linarith

lemma metallicCertificateObjective_strictMonoOn :
    StrictMonoOn metallicCertificateObjective (Set.Ioi 1) := by
  exact strictMonoOn_of_deriv_pos (convex_Ioi (1 : ℝ))
    metallicCertificateObjective_continuousOn
    (fun x hx => metallicCertificateObjective_deriv_pos hx)

/-- Paper-facing λ-parameter package for the continuous metallic Pareto frontier:
    the first clause records the `A = λ - λ⁻¹` rewrite and the closed forms for the two objectives,
    the second clause shows every `λ > 2` is strictly dominated by `λ = 2`,
    and the third clause shows that on `λ ∈ [φ, 2]` the compression and certificate objectives both
    increase with `λ`, so maximizing compression while minimizing certificate cost leaves the entire
    interval as the continuous Pareto image.
    prop:metallic-pareto-frontier-lambda -/
theorem paper_metallic_pareto_frontier_lambda :
    (∀ {lam : ℝ}, φ ≤ lam →
      metallicAOfLambda lam = lam - lam⁻¹ ∧
      lam ^ 2 - metallicAOfLambda lam * lam - 1 = 0 ∧
      Real.log ((metallicAOfLambda lam + 1) / lam) = metallicCompressionObjective lam ∧
      metallicCertificateObjective lam = metallicAOfLambda lam / Real.log lam) ∧
    (∀ {lam : ℝ}, 2 < lam →
      metallicCompressionObjective lam < metallicCompressionObjective 2 ∧
      metallicCertificateObjective 2 < metallicCertificateObjective lam) ∧
    (∀ {lam₁ lam₂ : ℝ}, lam₁ ∈ Set.Icc φ 2 → lam₂ ∈ Set.Icc φ 2 → lam₁ < lam₂ →
      metallicCompressionObjective lam₁ < metallicCompressionObjective lam₂ ∧
      metallicCertificateObjective lam₁ < metallicCertificateObjective lam₂) := by
  refine ⟨?_, ?_, ?_⟩
  · intro lam hlam
    have hlam0 : 0 < lam := lt_of_lt_of_le Real.goldenRatio_pos hlam
    refine ⟨rfl, ?_, ?_, by simp [metallicCertificateObjective, metallicAOfLambda]⟩
    · unfold metallicAOfLambda
      field_simp [hlam0.ne']
      ring
    · unfold metallicAOfLambda metallicCompressionObjective
      congr 1
      field_simp [hlam0.ne']
      ring
  · intro lam hlam
    have hlam0 : 0 < lam := by linarith
    have hinside : 1 + lam⁻¹ - lam⁻¹ ^ 2 < 5 / 4 := by
      have hnum : 0 < (lam - 2) ^ 2 := by
        have hneq : lam - 2 ≠ 0 := sub_ne_zero.mpr hlam.ne'
        exact sq_pos_iff.mpr hneq
      have hden : 0 < 4 * lam ^ 2 := by positivity
      have hquad : 0 < (lam - 2) ^ 2 / (4 * lam ^ 2) := div_pos hnum hden
      have hrew : 5 / 4 - (1 + lam⁻¹ - lam⁻¹ ^ 2) = (lam - 2) ^ 2 / (4 * lam ^ 2) := by
        field_simp [hlam0.ne']
        ring
      linarith
    have hlamOne : 1 ≤ lam := by linarith [Real.one_lt_goldenRatio]
    have hcomp :
        metallicCompressionObjective lam < metallicCompressionObjective 2 := by
      have hpos : 0 < 1 + lam⁻¹ - lam⁻¹ ^ 2 := metallicCompressionInside_pos hlamOne
      have hlog : Real.log (1 + lam⁻¹ - lam⁻¹ ^ 2) < Real.log (5 / 4 : ℝ) :=
        Real.log_lt_log hpos hinside
      have htwo : metallicCompressionObjective 2 = Real.log (5 / 4 : ℝ) := by
        norm_num [metallicCompressionObjective]
      rw [htwo]
      simpa [metallicCompressionObjective] using hlog
    have hkappa :
        metallicCertificateObjective 2 < metallicCertificateObjective lam := by
      have hlamIoi : lam ∈ Set.Ioi 1 := by
        show 1 < lam
        linarith
      exact metallicCertificateObjective_strictMonoOn
        (show (2 : ℝ) ∈ Set.Ioi 1 by norm_num) hlamIoi hlam
    exact ⟨hcomp, hkappa⟩
  · intro lam₁ lam₂ h₁ h₂ hlt
    have h₁φ : φ ≤ lam₁ := h₁.1
    have h₂φ : φ ≤ lam₂ := h₂.1
    have hlam₁0 : 0 < lam₁ := lt_of_lt_of_le Real.goldenRatio_pos h₁φ
    have hlam₂0 : 0 < lam₂ := lt_of_lt_of_le Real.goldenRatio_pos h₂φ
    have hprod : lam₁ * lam₂ - lam₁ - lam₂ < 0 := by
      have hlam₂one : 1 < lam₂ := by linarith [Real.one_lt_goldenRatio, h₂φ]
      have hstep : lam₁ * lam₂ - lam₁ - lam₂ < lam₂ ^ 2 - 2 * lam₂ := by
        nlinarith [hlt, hlam₂one]
      have htop : lam₂ ^ 2 - 2 * lam₂ ≤ 0 := by
        nlinarith [h₂.2]
      exact lt_of_lt_of_le hstep htop
    have hdiff :
        (1 + lam₂⁻¹ - lam₂⁻¹ ^ 2) - (1 + lam₁⁻¹ - lam₁⁻¹ ^ 2) =
          (lam₁ - lam₂) * (lam₁ * lam₂ - lam₁ - lam₂) / (lam₁ ^ 2 * lam₂ ^ 2) := by
      field_simp [hlam₁0.ne', hlam₂0.ne']
      ring
    have hdiffPos :
        0 < (lam₁ - lam₂) * (lam₁ * lam₂ - lam₁ - lam₂) / (lam₁ ^ 2 * lam₂ ^ 2) := by
      have hnum : 0 < (lam₁ - lam₂) * (lam₁ * lam₂ - lam₁ - lam₂) := by
        have hleft : lam₁ - lam₂ < 0 := sub_neg.mpr hlt
        exact mul_pos_of_neg_of_neg hleft hprod
      have hden : 0 < lam₁ ^ 2 * lam₂ ^ 2 := by positivity
      exact div_pos hnum hden
    have hinside :
        1 + lam₁⁻¹ - lam₁⁻¹ ^ 2 < 1 + lam₂⁻¹ - lam₂⁻¹ ^ 2 := by
      linarith [hdiff, hdiffPos]
    have h₁one : 1 ≤ lam₁ := by linarith [Real.one_lt_goldenRatio, h₁φ]
    have h₂one : 1 ≤ lam₂ := by linarith [Real.one_lt_goldenRatio, h₂φ]
    have hcomp :
        metallicCompressionObjective lam₁ < metallicCompressionObjective lam₂ := by
      have hpos₁ : 0 < 1 + lam₁⁻¹ - lam₁⁻¹ ^ 2 := metallicCompressionInside_pos h₁one
      have hpos₂ : 0 < 1 + lam₂⁻¹ - lam₂⁻¹ ^ 2 := metallicCompressionInside_pos h₂one
      simpa [metallicCompressionObjective] using Real.log_lt_log hpos₁ hinside
    have hkappa :
        metallicCertificateObjective lam₁ < metallicCertificateObjective lam₂ := by
      have hlam₁Ioi : lam₁ ∈ Set.Ioi 1 := by
        show 1 < lam₁
        linarith [Real.one_lt_goldenRatio, h₁φ]
      have hlam₂Ioi : lam₂ ∈ Set.Ioi 1 := by
        show 1 < lam₂
        linarith [Real.one_lt_goldenRatio, h₂φ]
      exact metallicCertificateObjective_strictMonoOn hlam₁Ioi hlam₂Ioi hlt
    exact ⟨hcomp, hkappa⟩

end Omega.Folding.MetallicParetoFrontier
