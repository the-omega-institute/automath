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

/-- Indicator of a finite subset of the state space. -/
noncomputable def setIndicator (A : Finset β) (b : β) : ℝ :=
  if b ∈ A then 1 else 0

/-- Event gap for a candidate subset used to test total variation. -/
noncomputable def eventGap [Fintype β] (Ω : Finset α) (X Y : α → β) (A : Finset β) : ℝ :=
  |expectation Ω (fun ω => setIndicator A (X ω)) -
      expectation Ω (fun ω => setIndicator A (Y ω))|

/-- Finite-state total variation between the pushforwards of `X` and `Y`, written as the maximum
test-set gap over all subsets of the state space. -/
noncomputable def pushforwardTvDistance [Fintype β] (Ω : Finset α) (X Y : α → β) : ℝ :=
  (((Finset.univ : Finset β).powerset).sup' (by simp) fun A : Finset β => eventGap Ω X Y A)

/-- Data for the optimality statement: a finite state space together with a witness subset whose
gap saturates the coupling error. -/
structure CurvatureTvOptimalData where
  α : Type*
  β : Type*
  instFintypeβ : Fintype β
  instDecEqβ : DecidableEq β
  Ω : Finset α
  hΩ : 0 < Ω.card
  X : α → β
  Y : α → β
  witnessSet : Finset β
  witnessRealizesError :
    eventGap Ω X Y witnessSet = probability Ω (fun ω => X ω ≠ Y ω)

attribute [instance] CurvatureTvOptimalData.instFintypeβ
attribute [instance] CurvatureTvOptimalData.instDecEqβ

/-- The curvature error is the disagreement probability of the coupled variables. -/
noncomputable def CurvatureTvOptimalData.curvatureError (D : CurvatureTvOptimalData) : ℝ :=
  probability D.Ω (fun ω => D.X ω ≠ D.Y ω)

/-- Total variation of the two pushforwards. -/
noncomputable def CurvatureTvOptimalData.tvDistance (D : CurvatureTvOptimalData) : ℝ :=
  pushforwardTvDistance D.Ω D.X D.Y

/-- The coupling error bounds the pushforward total variation. -/
def CurvatureTvOptimalData.tvDistanceLeCurvatureError (D : CurvatureTvOptimalData) : Prop :=
  D.tvDistance ≤ D.curvatureError

/-- The witness subset saturates the coupling bound, so the constant is optimal. -/
def CurvatureTvOptimalData.boundSharp (D : CurvatureTvOptimalData) : Prop :=
  D.tvDistance = D.curvatureError

theorem indicator_gap_pointwise_le_neIndicator [Fintype β] (A : Finset β) (X Y : α → β)
    (ω : α) :
    |setIndicator A (X ω) - setIndicator A (Y ω)| ≤ neIndicator X Y ω := by
  unfold setIndicator neIndicator
  by_cases hxy : X ω = Y ω
  · simp [hxy]
  · by_cases hx : X ω ∈ A <;> by_cases hy : Y ω ∈ A <;> simp [hxy, hx, hy]

theorem eventGap_le_curvatureError [Fintype β] (Ω : Finset α) (hΩ : 0 < Ω.card)
    (X Y : α → β) (A : Finset β) :
    eventGap Ω X Y A ≤ probability Ω (fun ω => X ω ≠ Y ω) := by
  unfold eventGap
  have h1 := abs_expectation_sub_le Ω
    (fun ω => setIndicator A (X ω)) (fun ω => setIndicator A (Y ω))
  have hcard_pos : (0 : ℝ) < (Ω.card : ℝ) := by
    exact_mod_cast hΩ
  have h2 : expectation Ω (fun ω => |setIndicator A (X ω) - setIndicator A (Y ω)|) ≤
      expectation Ω (neIndicator X Y) := by
    unfold expectation
    apply div_le_div_of_nonneg_right _ hcard_pos.le
    apply Finset.sum_le_sum
    intro ω _
    exact indicator_gap_pointwise_le_neIndicator A X Y ω
  have h3 : expectation Ω (neIndicator X Y) =
      probability Ω (fun ω => X ω ≠ Y ω) :=
    (probability_eq_expectation_neIndicator Ω X Y).symm
  linarith

theorem pushforwardTvDistance_le_curvatureError [Fintype β] (Ω : Finset α) (hΩ : 0 < Ω.card)
    (X Y : α → β) :
    pushforwardTvDistance Ω X Y ≤ probability Ω (fun ω => X ω ≠ Y ω) := by
  simpa [pushforwardTvDistance] using
    (Finset.sup'_le (s := ((Finset.univ : Finset β).powerset)) (H := by simp)
      (f := fun A : Finset β => eventGap Ω X Y A)
      (a := probability Ω (fun ω => X ω ≠ Y ω))
      (by
        intro A hA
        exact eventGap_le_curvatureError Ω hΩ X Y A))

theorem eventGap_le_pushforwardTvDistance [Fintype β] (Ω : Finset α) (X Y : α → β)
    (A : Finset β) :
    eventGap Ω X Y A ≤ pushforwardTvDistance Ω X Y := by
  have hA : A ∈ (Finset.univ : Finset β).powerset := by
    rw [Finset.mem_powerset]
    intro b hb
    simp
  simpa [pushforwardTvDistance] using
    (Finset.le_sup' (s := ((Finset.univ : Finset β).powerset))
      (f := fun B : Finset β => eventGap Ω X Y B) hA)

/-- The coupling inequality bounds the pushforward total variation by the curvature error, and an
explicit witness subset shows that this constant is sharp.
    prop:pom-curvature-tv-optimal -/
theorem paper_pom_curvature_tv_optimal (D : CurvatureTvOptimalData) :
    D.tvDistanceLeCurvatureError ∧ D.boundSharp := by
  constructor
  · dsimp [CurvatureTvOptimalData.tvDistanceLeCurvatureError,
      CurvatureTvOptimalData.tvDistance, CurvatureTvOptimalData.curvatureError]
    exact pushforwardTvDistance_le_curvatureError D.Ω D.hΩ D.X D.Y
  · dsimp [CurvatureTvOptimalData.boundSharp]
    apply le_antisymm
    · dsimp [CurvatureTvOptimalData.tvDistance, CurvatureTvOptimalData.curvatureError]
      exact pushforwardTvDistance_le_curvatureError D.Ω D.hΩ D.X D.Y
    · dsimp [CurvatureTvOptimalData.curvatureError, CurvatureTvOptimalData.tvDistance]
      simpa [D.witnessRealizesError] using
        (eventGap_le_pushforwardTvDistance D.Ω D.X D.Y D.witnessSet)

end Omega.POM.CouplingExpectationBound
