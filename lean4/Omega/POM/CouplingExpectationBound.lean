import Mathlib.Tactic

namespace Omega.POM.CouplingExpectationBound

open Finset

variable {α β : Type*} [DecidableEq β]

/-- Uniform expectation over a finite set, valued in `ℝ`.
    prop:pom-gauge-curvature-shadow-bound -/
noncomputable def expectation (Ω : Finset α) (g : α → ℝ) : ℝ :=
  (∑ ω ∈ Ω, g ω) / Ω.card

/-- Uniform probability of an event.
    prop:pom-gauge-curvature-shadow-bound -/
noncomputable def probability (Ω : Finset α) (A : α → Prop) [DecidablePred A] : ℝ :=
  ((Ω.filter A).card : ℝ) / Ω.card

/-- Inequality indicator.
    prop:pom-gauge-curvature-shadow-bound -/
noncomputable def neIndicator (X Y : α → β) (ω : α) : ℝ :=
  if X ω = Y ω then 0 else 1

/-- Pointwise bound: `|f(X) - f(Y)| ≤ 2M · 1[X ≠ Y]`.
    prop:pom-gauge-curvature-shadow-bound -/
theorem pointwise_diff_le (f : β → ℝ) (M : ℝ) (_hM : 0 ≤ M)
    (hf : ∀ b, |f b| ≤ M) (X Y : α → β) (ω : α) :
    |f (X ω) - f (Y ω)| ≤ 2 * M * neIndicator X Y ω := by
  unfold neIndicator
  by_cases h : X ω = Y ω
  · rw [h]
    simp
  · simp [h]
    have h1 : |f (X ω)| ≤ M := hf (X ω)
    have h2 : |f (Y ω)| ≤ M := hf (Y ω)
    have habs : |f (X ω) - f (Y ω)| ≤ |f (X ω)| + |f (Y ω)| := abs_sub _ _
    linarith

/-- Triangle-type bound: `|E[g] - E[h]| ≤ E[|g - h|]`.
    prop:pom-gauge-curvature-shadow-bound -/
theorem abs_expectation_sub_le (Ω : Finset α) (g h : α → ℝ) :
    |expectation Ω g - expectation Ω h| ≤
      expectation Ω (fun ω => |g ω - h ω|) := by
  unfold expectation
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div]
  rw [abs_of_nonneg (by exact_mod_cast Nat.zero_le _ : (0 : ℝ) ≤ (Ω.card : ℝ))]
  rcases Nat.eq_zero_or_pos Ω.card with hzero | hpos
  · simp [hzero]
  · apply div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _)
    exact_mod_cast hpos.le

/-- Probability of disagreement equals expectation of the inequality indicator.
    prop:pom-gauge-curvature-shadow-bound -/
theorem probability_eq_expectation_neIndicator (Ω : Finset α) (X Y : α → β) :
    probability Ω (fun ω => X ω ≠ Y ω) = expectation Ω (neIndicator X Y) := by
  unfold probability expectation neIndicator
  congr 1
  rw [show (∑ ω ∈ Ω, if X ω = Y ω then (0 : ℝ) else 1) =
        ∑ ω ∈ Ω, if X ω ≠ Y ω then (1 : ℝ) else 0 from
      Finset.sum_congr rfl (fun ω _ => by by_cases hxy : X ω = Y ω <;> simp [hxy])]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]

/-- Coupling expectation bound: `|E[f(X)] - E[f(Y)]| ≤ 2M · P[X ≠ Y]`.
    prop:pom-gauge-curvature-shadow-bound -/
theorem coupling_expectation_bound (Ω : Finset α) (hΩ : 0 < Ω.card)
    (f : β → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ b, |f b| ≤ M) (X Y : α → β) :
    |expectation Ω (fun ω => f (X ω)) - expectation Ω (fun ω => f (Y ω))| ≤
      2 * M * probability Ω (fun ω => X ω ≠ Y ω) := by
  have hcard_pos : (0 : ℝ) < (Ω.card : ℝ) := by exact_mod_cast hΩ
  have hcard_ne : (Ω.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  -- Step 1: |E[f X] - E[f Y]| ≤ E[|f(X) - f(Y)|]
  have h1 := abs_expectation_sub_le Ω (fun ω => f (X ω)) (fun ω => f (Y ω))
  -- Step 2: E[|f(X) - f(Y)|] ≤ E[2M · 1[X ≠ Y]]
  have h2 : expectation Ω (fun ω => |f (X ω) - f (Y ω)|) ≤
      expectation Ω (fun ω => 2 * M * neIndicator X Y ω) := by
    unfold expectation
    apply div_le_div_of_nonneg_right _ hcard_pos.le
    apply Finset.sum_le_sum
    intro ω _
    exact pointwise_diff_le f M hM hf X Y ω
  -- Step 3: E[2M · 1[X ≠ Y]] = 2M · E[1[X ≠ Y]] = 2M · P[X ≠ Y]
  have h3 : expectation Ω (fun ω => 2 * M * neIndicator X Y ω) =
      2 * M * expectation Ω (neIndicator X Y) := by
    unfold expectation
    rw [← Finset.mul_sum]
    rw [mul_div_assoc]
  have h4 : expectation Ω (neIndicator X Y) =
      probability Ω (fun ω => X ω ≠ Y ω) :=
    (probability_eq_expectation_neIndicator Ω X Y).symm
  linarith [h1, h2, h3, h4 ▸ h3]

/-- Paper package: POM gauge-curvature shadow bound.
    prop:pom-gauge-curvature-shadow-bound -/
theorem paper_pom_gauge_curvature_shadow_bound (Ω : Finset α) (hΩ : 0 < Ω.card)
    (f : β → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ b, |f b| ≤ M) (X Y : α → β) :
    |expectation Ω (fun ω => f (X ω)) - expectation Ω (fun ω => f (Y ω))| ≤
      2 * M * probability Ω (fun ω => X ω ≠ Y ω) :=
  coupling_expectation_bound Ω hΩ f M hM hf X Y

end Omega.POM.CouplingExpectationBound
