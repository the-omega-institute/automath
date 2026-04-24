import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.POM.CoarsegrainingMajorizationSchur

namespace Omega.POM

/-- The Hellinger endpoint profile associated with the ordered weight pair `(a,b)`. -/
noncomputable def pom_diagonal_rate_pi_majorization_chain_piHalf (a b : ℝ) : ℝ × ℝ :=
  let s := Real.sqrt a + Real.sqrt b
  (Real.sqrt a / s, Real.sqrt b / s)

/-- A concrete monotone interpolation from the Hellinger endpoint `π_{1/2}` to the target weight
pair `(a,b)`. -/
noncomputable def pom_diagonal_rate_pi_majorization_chain_pi (a b δ : ℝ) : ℝ × ℝ :=
  let πhalf := pom_diagonal_rate_pi_majorization_chain_piHalf a b
  ((1 - δ) * πhalf.1 + δ * a, (1 - δ) * πhalf.2 + δ * b)

private lemma pom_diagonal_rate_pi_majorization_chain_piHalf_sum
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (pom_diagonal_rate_pi_majorization_chain_piHalf a b).1 +
        (pom_diagonal_rate_pi_majorization_chain_piHalf a b).2 =
      1 := by
  have hs_pos : 0 < Real.sqrt a + Real.sqrt b := by positivity
  simp [pom_diagonal_rate_pi_majorization_chain_piHalf]
  field_simp [hs_pos.ne']

private lemma pom_diagonal_rate_pi_majorization_chain_piHalf_first_le
    {a b : ℝ} (hab : b ≤ a) (hb : 0 < b) (hsum : a + b = 1) :
    (pom_diagonal_rate_pi_majorization_chain_piHalf a b).1 ≤ a := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have ha_nonneg : 0 ≤ a := ha.le
  have hb_nonneg : 0 ≤ b := hb.le
  have hs_pos : 0 < Real.sqrt a + Real.sqrt b := by positivity
  have hsqrt_le : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt hab
  have hfactor :
      a * (Real.sqrt a + Real.sqrt b) - Real.sqrt a =
        Real.sqrt a * Real.sqrt b * (Real.sqrt a - Real.sqrt b) := by
    nlinarith [Real.sq_sqrt ha_nonneg, Real.sq_sqrt hb_nonneg, hsum]
  have hineq :
      Real.sqrt a ≤ a * (Real.sqrt a + Real.sqrt b) := by
    have hnonneg :
        0 ≤ a * (Real.sqrt a + Real.sqrt b) - Real.sqrt a := by
      rw [hfactor]
      have :
          0 ≤ Real.sqrt a * Real.sqrt b * (Real.sqrt a - Real.sqrt b) := by
        exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (sub_nonneg.mpr hsqrt_le)
      exact this
    linarith
  have := (_root_.div_le_iff₀ hs_pos).2 hineq
  simpa [pom_diagonal_rate_pi_majorization_chain_piHalf] using this

private lemma pom_diagonal_rate_pi_majorization_chain_pi_sum
    {a b δ : ℝ} (ha : 0 < a) (hb : 0 < b) (hsum : a + b = 1) :
    (pom_diagonal_rate_pi_majorization_chain_pi a b δ).1 +
        (pom_diagonal_rate_pi_majorization_chain_pi a b δ).2 =
      1 := by
  have hhalf :
      (pom_diagonal_rate_pi_majorization_chain_piHalf a b).1 +
          (pom_diagonal_rate_pi_majorization_chain_piHalf a b).2 =
        1 :=
    pom_diagonal_rate_pi_majorization_chain_piHalf_sum ha hb
  have hmain :
      ((1 - δ) * (pom_diagonal_rate_pi_majorization_chain_piHalf a b).1 + δ * a) +
          ((1 - δ) * (pom_diagonal_rate_pi_majorization_chain_piHalf a b).2 + δ * b) =
        (1 - δ) * 1 + δ * 1 := by
    calc
      ((1 - δ) * (pom_diagonal_rate_pi_majorization_chain_piHalf a b).1 + δ * a) +
            ((1 - δ) * (pom_diagonal_rate_pi_majorization_chain_piHalf a b).2 + δ * b) =
          (1 - δ) *
              ((pom_diagonal_rate_pi_majorization_chain_piHalf a b).1 +
                (pom_diagonal_rate_pi_majorization_chain_piHalf a b).2) +
            δ * (a + b) := by ring
      _ = (1 - δ) * 1 + δ * 1 := by rw [hhalf, hsum]
  simpa [pom_diagonal_rate_pi_majorization_chain_pi] using hmain

private lemma pom_diagonal_rate_pi_majorization_chain_pi_first_mono
    {a b δ₁ δ₂ : ℝ} (hab : b ≤ a) (hb : 0 < b) (hsum : a + b = 1)
    (hδ : δ₁ ≤ δ₂) :
    (pom_diagonal_rate_pi_majorization_chain_pi a b δ₁).1 ≤
      (pom_diagonal_rate_pi_majorization_chain_pi a b δ₂).1 := by
  have hhalf_le :
      (pom_diagonal_rate_pi_majorization_chain_piHalf a b).1 ≤ a :=
    pom_diagonal_rate_pi_majorization_chain_piHalf_first_le hab hb hsum
  have hrew :
      (pom_diagonal_rate_pi_majorization_chain_pi a b δ₂).1 -
          (pom_diagonal_rate_pi_majorization_chain_pi a b δ₁).1 =
        (δ₂ - δ₁) * (a - (pom_diagonal_rate_pi_majorization_chain_piHalf a b).1) := by
    simp [pom_diagonal_rate_pi_majorization_chain_pi]
    ring
  have hnonneg :
      0 ≤
        (pom_diagonal_rate_pi_majorization_chain_pi a b δ₂).1 -
          (pom_diagonal_rate_pi_majorization_chain_pi a b δ₁).1 := by
    rw [hrew]
    exact mul_nonneg (sub_nonneg.mpr hδ) (sub_nonneg.mpr hhalf_le)
  linarith

/-- Paper label: `thm:pom-diagonal-rate-pi-majorization-chain`. For an ordered full-support
two-point weight vector, the concrete interpolation between the Hellinger endpoint and the weight
vector is monotone in the Hardy-Littlewood-Polya order; in particular every intermediate profile
lies between `π_{1/2}` and `w`, and increasing the interpolation parameter strengthens the
majorization. -/
theorem paper_pom_diagonal_rate_pi_majorization_chain
    (a b δ₁ δ₂ : ℝ)
    (hab : b ≤ a) (hb : 0 < b) (hsum : a + b = 1)
    (hδ₁ : 0 ≤ δ₁) (hδ₁₂ : δ₁ ≤ δ₂) (hδ₂ : δ₂ ≤ 1) :
    pairMajorizes (pom_diagonal_rate_pi_majorization_chain_pi a b δ₂)
      (pom_diagonal_rate_pi_majorization_chain_pi a b δ₁) ∧
    pairMajorizes (fineFiberPair a b) (pom_diagonal_rate_pi_majorization_chain_pi a b δ₂) ∧
    pairMajorizes (pom_diagonal_rate_pi_majorization_chain_pi a b δ₁)
      (pom_diagonal_rate_pi_majorization_chain_piHalf a b) := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have hhalf_le :
      (pom_diagonal_rate_pi_majorization_chain_piHalf a b).1 ≤ a :=
    pom_diagonal_rate_pi_majorization_chain_piHalf_first_le hab hb hsum
  have hpi₁_sum :
      (pom_diagonal_rate_pi_majorization_chain_pi a b δ₁).1 +
          (pom_diagonal_rate_pi_majorization_chain_pi a b δ₁).2 =
        1 :=
    pom_diagonal_rate_pi_majorization_chain_pi_sum ha hb hsum
  have hpi₂_sum :
      (pom_diagonal_rate_pi_majorization_chain_pi a b δ₂).1 +
          (pom_diagonal_rate_pi_majorization_chain_pi a b δ₂).2 =
        1 :=
    pom_diagonal_rate_pi_majorization_chain_pi_sum ha hb hsum
  have hhalf_sum :
      (pom_diagonal_rate_pi_majorization_chain_piHalf a b).1 +
          (pom_diagonal_rate_pi_majorization_chain_piHalf a b).2 =
        1 :=
    pom_diagonal_rate_pi_majorization_chain_piHalf_sum ha hb
  have hchain :
      (pom_diagonal_rate_pi_majorization_chain_pi a b δ₁).1 ≤
        (pom_diagonal_rate_pi_majorization_chain_pi a b δ₂).1 :=
    pom_diagonal_rate_pi_majorization_chain_pi_first_mono hab hb hsum hδ₁₂
  have hw_upper :
      (pom_diagonal_rate_pi_majorization_chain_pi a b δ₂).1 ≤ a := by
    have hrew :
        a - (pom_diagonal_rate_pi_majorization_chain_pi a b δ₂).1 =
          (1 - δ₂) * (a - (pom_diagonal_rate_pi_majorization_chain_piHalf a b).1) := by
      simp [pom_diagonal_rate_pi_majorization_chain_pi]
      ring
    have hnonneg :
        0 ≤ a - (pom_diagonal_rate_pi_majorization_chain_pi a b δ₂).1 := by
      rw [hrew]
      exact mul_nonneg (sub_nonneg.mpr hδ₂) (sub_nonneg.mpr hhalf_le)
    linarith
  have hhalf_lower :
      (pom_diagonal_rate_pi_majorization_chain_piHalf a b).1 ≤
        (pom_diagonal_rate_pi_majorization_chain_pi a b δ₁).1 := by
    have hrew :
        (pom_diagonal_rate_pi_majorization_chain_pi a b δ₁).1 -
            (pom_diagonal_rate_pi_majorization_chain_piHalf a b).1 =
          δ₁ * (a - (pom_diagonal_rate_pi_majorization_chain_piHalf a b).1) := by
      simp [pom_diagonal_rate_pi_majorization_chain_pi]
      ring
    have hnonneg :
        0 ≤
          (pom_diagonal_rate_pi_majorization_chain_pi a b δ₁).1 -
            (pom_diagonal_rate_pi_majorization_chain_piHalf a b).1 := by
      rw [hrew]
      exact mul_nonneg hδ₁ (sub_nonneg.mpr hhalf_le)
    linarith
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨hchain, ?_⟩
    linarith [hpi₁_sum, hpi₂_sum]
  · refine ⟨hw_upper, ?_⟩
    have hsum_eq :
        (pom_diagonal_rate_pi_majorization_chain_pi a b δ₂).1 +
            (pom_diagonal_rate_pi_majorization_chain_pi a b δ₂).2 =
          a + b := by
      linarith [hpi₂_sum, hsum]
    simpa [fineFiberPair] using hsum_eq
  · refine ⟨hhalf_lower, ?_⟩
    have hsum_eq :
        (pom_diagonal_rate_pi_majorization_chain_piHalf a b).1 +
            (pom_diagonal_rate_pi_majorization_chain_piHalf a b).2 =
          (pom_diagonal_rate_pi_majorization_chain_pi a b δ₁).1 +
            (pom_diagonal_rate_pi_majorization_chain_pi a b δ₁).2 := by
      linarith [hpi₁_sum, hhalf_sum]
    exact hsum_eq

end Omega.POM
