import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.Entropy

namespace Omega.Folding

/-- The Bernoulli parameter extracted from the escort last-bit reduction. -/
noncomputable def killoEscortTheta (q : ℝ) : ℝ :=
  1 / (1 + Real.exp ((q + 1) * Real.log Real.goldenRatio))

/-- The Bernoulli Rényi divergence attached to the escort limiting family. -/
noncomputable def killoEscortRenyiLimit (α p q : ℝ) : ℝ :=
  (Real.log
      (killoEscortTheta q ^ α * killoEscortTheta p ^ (1 - α) +
        (1 - killoEscortTheta q) ^ α * (1 - killoEscortTheta p) ^ (1 - α))) / (α - 1)

/-- The KL specialization of the escort Bernoulli limit. -/
noncomputable def killoEscortKLDivergence (p q : ℝ) : ℝ :=
  killoEscortTheta q * Real.log (killoEscortTheta q / killoEscortTheta p) +
    (1 - killoEscortTheta q) * Real.log ((1 - killoEscortTheta q) / (1 - killoEscortTheta p))

/-- Fisher information along the one-parameter escort logistic curve. -/
noncomputable def killoEscortFisher (q : ℝ) : ℝ :=
  (deriv killoEscortTheta q) ^ 2 / (killoEscortTheta q * (1 - killoEscortTheta q))

lemma killoEscortTheta_pos (q : ℝ) : 0 < killoEscortTheta q := by
  unfold killoEscortTheta
  positivity

lemma killoEscortTheta_lt_one (q : ℝ) : killoEscortTheta q < 1 := by
  unfold killoEscortTheta
  have hone : 1 < 1 + Real.exp ((q + 1) * Real.log Real.goldenRatio) := by
    have hexp : 0 < Real.exp ((q + 1) * Real.log Real.goldenRatio) := Real.exp_pos _
    linarith
  simpa using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hone)

lemma killoEscortTheta_one_sub (q : ℝ) :
    1 - killoEscortTheta q =
      Real.exp ((q + 1) * Real.log Real.goldenRatio) /
        (1 + Real.exp ((q + 1) * Real.log Real.goldenRatio)) := by
  have hden : (1 + Real.exp ((q + 1) * Real.log Real.goldenRatio) : ℝ) ≠ 0 := by positivity
  unfold killoEscortTheta
  field_simp [hden]
  ring

lemma deriv_killoEscortTheta (q : ℝ) :
    deriv killoEscortTheta q =
      -(Real.log Real.goldenRatio) * killoEscortTheta q * (1 - killoEscortTheta q) := by
  let L : ℝ := Real.log Real.goldenRatio
  have hArg : HasDerivAt (fun x : ℝ => (x + 1) * L) L q := by
    simpa [L, one_mul] using (((hasDerivAt_id q).add_const 1).mul_const L)
  have hExp :
      HasDerivAt (fun x : ℝ => Real.exp ((x + 1) * L)) (Real.exp ((q + 1) * L) * L) q := by
    simpa [L, mul_comm] using (Real.hasDerivAt_exp ((q + 1) * L)).comp q hArg
  have hDen :
      HasDerivAt (fun x : ℝ => 1 + Real.exp ((x + 1) * L)) (Real.exp ((q + 1) * L) * L) q := by
    convert (hasDerivAt_const q (1 : ℝ)).add hExp using 1 <;> simp
  have hTheta :
      HasDerivAt killoEscortTheta
        (-(Real.exp ((q + 1) * L) * L) / (1 + Real.exp ((q + 1) * L)) ^ 2) q := by
    have hne : (1 + Real.exp ((q + 1) * L) : ℝ) ≠ 0 := by positivity
    unfold killoEscortTheta
    simpa [one_div] using hDen.inv hne
  have hderiv := hTheta.deriv
  have htheta :
      killoEscortTheta q * (1 - killoEscortTheta q) =
        Real.exp ((q + 1) * L) / (1 + Real.exp ((q + 1) * L)) ^ 2 := by
    have hden : (1 + Real.exp ((q + 1) * L) : ℝ) ≠ 0 := by positivity
    rw [killoEscortTheta_one_sub]
    unfold killoEscortTheta
    field_simp [hden]
    ring
  calc
    deriv killoEscortTheta q =
        -(Real.exp ((q + 1) * L) * L) / (1 + Real.exp ((q + 1) * L)) ^ 2 := hderiv
    _ = -L * (Real.exp ((q + 1) * L) / (1 + Real.exp ((q + 1) * L)) ^ 2) := by ring
    _ = -L * (killoEscortTheta q * (1 - killoEscortTheta q)) := by rw [htheta]
    _ = -(Real.log Real.goldenRatio) * killoEscortTheta q * (1 - killoEscortTheta q) := by
          simp [L, mul_assoc]

lemma killoEscortFisher_closed_form (q : ℝ) :
    killoEscortFisher q =
      (Real.log Real.goldenRatio) ^ 2 * killoEscortTheta q * (1 - killoEscortTheta q) := by
  have hprod_ne : killoEscortTheta q * (1 - killoEscortTheta q) ≠ 0 := by
    have hθ : 0 < killoEscortTheta q := killoEscortTheta_pos q
    have h1θ : 0 < 1 - killoEscortTheta q := sub_pos.mpr (killoEscortTheta_lt_one q)
    exact mul_ne_zero hθ.ne' h1θ.ne'
  rw [killoEscortFisher, deriv_killoEscortTheta]
  field_simp [hprod_ne]

lemma killoEscortFisher_strictAnti {q₁ q₂ : ℝ} (hq₁ : 0 ≤ q₁) (hq : q₁ < q₂) :
    killoEscortFisher q₂ < killoEscortFisher q₁ := by
  let L : ℝ := Real.log Real.goldenRatio
  let a : ℝ := Real.exp ((q₁ + 1) * L)
  let b : ℝ := Real.exp ((q₂ + 1) * L)
  have hL : 0 < L := Omega.Entropy.log_goldenRatio_pos
  have ha_gt_one : 1 < a := by
    have harg : 0 < (q₁ + 1) * L := by
      have hq₁' : 0 < q₁ + 1 := by linarith
      nlinarith
    simpa [a] using Real.one_lt_exp_iff.mpr harg
  have hb_gt_one : 1 < b := by
    have harg : 0 < (q₂ + 1) * L := by
      have : 0 < q₂ + 1 := by linarith
      nlinarith
    simpa [b] using Real.one_lt_exp_iff.mpr harg
  have hab : a < b := by
    refine Real.exp_strictMono ?_
    dsimp [a, b]
    nlinarith [hq, hL]
  have hcross : b * (1 + a) ^ 2 < a * (1 + b) ^ 2 := by
    have hid : a * (1 + b) ^ 2 - b * (1 + a) ^ 2 = (b - a) * (a * b - 1) := by ring
    have hpos : 0 < a * (1 + b) ^ 2 - b * (1 + a) ^ 2 := by
      have hba : 0 < b - a := sub_pos.mpr hab
      have hab1 : 0 < a * b - 1 := by nlinarith [ha_gt_one, hb_gt_one]
      rw [hid]
      positivity
    linarith
  have hfrac : b / (1 + b) ^ 2 < a / (1 + a) ^ 2 := by
    have hane : (1 + a : ℝ) ≠ 0 := by positivity
    have hbne : (1 + b : ℝ) ≠ 0 := by positivity
    field_simp [hane, hbne]
    linarith
  have htheta₁ :
      killoEscortTheta q₁ * (1 - killoEscortTheta q₁) = a / (1 + a) ^ 2 := by
    have hden : (1 + Real.exp ((q₁ + 1) * L) : ℝ) ≠ 0 := by positivity
    rw [killoEscortTheta_one_sub]
    unfold killoEscortTheta
    dsimp [a]
    field_simp [hden]
    ring
  have htheta₂ :
      killoEscortTheta q₂ * (1 - killoEscortTheta q₂) = b / (1 + b) ^ 2 := by
    have hden : (1 + Real.exp ((q₂ + 1) * L) : ℝ) ≠ 0 := by positivity
    rw [killoEscortTheta_one_sub]
    unfold killoEscortTheta
    dsimp [b]
    field_simp [hden]
    ring
  have hcore :
      killoEscortTheta q₂ * (1 - killoEscortTheta q₂) <
        killoEscortTheta q₁ * (1 - killoEscortTheta q₁) := by
    rw [htheta₂, htheta₁]
    exact hfrac
  calc
    killoEscortFisher q₂ =
        (Real.log Real.goldenRatio) ^ 2 * (killoEscortTheta q₂ * (1 - killoEscortTheta q₂)) := by
          rw [killoEscortFisher_closed_form]
          ring
    _ < (Real.log Real.goldenRatio) ^ 2 * (killoEscortTheta q₁ * (1 - killoEscortTheta q₁)) := by
          exact mul_lt_mul_of_pos_left hcore (by positivity)
    _ = killoEscortFisher q₁ := by
          rw [killoEscortFisher_closed_form]
          ring

/-- The escort temperature family collapses to a one-bit Bernoulli logistic curve: the Rényi and
KL limit formulas are the Bernoulli closed forms at `θ(q)`, the logistic differential equation
holds exactly, and the associated Fisher information is strictly decreasing on `[0, ∞)`. -/
theorem paper_killo_fold_bin_escort_renyi_logistic_geometry :
    (∀ p q α : ℝ, 0 ≤ p → 0 ≤ q → 0 < α → α ≠ 1 →
      killoEscortRenyiLimit α p q =
        Real.log
            (killoEscortTheta q ^ α * killoEscortTheta p ^ (1 - α) +
              (1 - killoEscortTheta q) ^ α * (1 - killoEscortTheta p) ^ (1 - α)) /
          (α - 1)) ∧
      (∀ p q : ℝ, 0 ≤ p → 0 ≤ q →
        killoEscortKLDivergence p q =
          killoEscortTheta q * Real.log (killoEscortTheta q / killoEscortTheta p) +
            (1 - killoEscortTheta q) *
              Real.log ((1 - killoEscortTheta q) / (1 - killoEscortTheta p))) ∧
      (∀ q : ℝ, 0 ≤ q →
        0 < killoEscortTheta q ∧
          killoEscortTheta q < 1 ∧
          deriv killoEscortTheta q =
            -(Real.log Real.goldenRatio) * killoEscortTheta q * (1 - killoEscortTheta q) ∧
          killoEscortFisher q =
            (Real.log Real.goldenRatio) ^ 2 * killoEscortTheta q * (1 - killoEscortTheta q)) ∧
      (∀ ⦃q₁ q₂ : ℝ⦄, 0 ≤ q₁ → q₁ < q₂ → killoEscortFisher q₂ < killoEscortFisher q₁) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p q α hp hq hα hα_ne
    rfl
  · intro p q hp hq
    rfl
  · intro q hq
    exact ⟨killoEscortTheta_pos q, killoEscortTheta_lt_one q, deriv_killoEscortTheta q,
      killoEscortFisher_closed_form q⟩
  · intro q₁ q₂ hq₁ hq
    exact killoEscortFisher_strictAnti hq₁ hq

end Omega.Folding
