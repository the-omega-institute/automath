import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.MultiplicityCompositionMomentHierarchyRationalGrowth

namespace Omega.POM

noncomputable section

/-- Real-parameter continuation of the moment-hierarchy weight. -/
def pomRealQWeight (q : ℝ) : ℝ :=
  q + 1

/-- The real-parameter two-term series used to define the pressure root. -/
def pomRealQSeries (q ρ : ℝ) : ℝ :=
  pomRealQWeight q * ρ + pomRealQWeight q * ρ ^ (2 : Nat)

/-- Dominant positive root of `λ² - w_q λ - w_q = 0` for the real weight `w_q = q + 1`. -/
def pomRealQDominantRoot (q : ℝ) : ℝ :=
  (pomRealQWeight q + Real.sqrt (pomRealQWeight q ^ (2 : Nat) + 4 * pomRealQWeight q)) / 2

/-- The positive solution `ρ(q) ∈ (0,1)` of `W_q(ρ) = 1`, written as the reciprocal Perron root. -/
def pomRealQRoot (q : ℝ) : ℝ :=
  (pomRealQDominantRoot q)⁻¹

/-- The corresponding pressure `log λ(q) = - log ρ(q)`. -/
def pomRealQPressure (q : ℝ) : ℝ :=
  Real.log (pomRealQDominantRoot q)

/-- Real-parameter pressure package: the root `ρ(q)` is the unique positive solution of
`W_q(ρ) = 1`, it matches the integer moment-hierarchy root, it decreases strictly with `q`, and
the pressure is the negative logarithm of the root. -/
def pomMultiplicityRealQPressureStatement : Prop :=
  (∀ q : ℝ, 0 < q →
    0 < pomRealQRoot q ∧
      pomRealQRoot q < 1 ∧
      pomRealQSeries q (pomRealQRoot q) = 1 ∧
      ∀ ρ : ℝ, 0 < ρ → pomRealQSeries q ρ = 1 → ρ = pomRealQRoot q) ∧
    (∀ n : ℕ, pomRealQRoot n = (pomMomentHierarchyDominantRoot n)⁻¹) ∧
    (∀ q₁ q₂ : ℝ, 0 < q₁ → q₁ < q₂ → pomRealQRoot q₂ < pomRealQRoot q₁) ∧
    (∀ q : ℝ, 0 < q → pomRealQPressure q = -Real.log (pomRealQRoot q))

private lemma pomRealQWeight_pos {q : ℝ} (hq : 0 < q) : 0 < pomRealQWeight q := by
  unfold pomRealQWeight
  linarith

private lemma pomRealQWeight_nonneg {q : ℝ} (hq : 0 < q) : 0 ≤ pomRealQWeight q := by
  exact (pomRealQWeight_pos hq).le

private lemma pomRealQDominantRoot_sq {q : ℝ} (hq : 0 < q) :
    pomRealQDominantRoot q ^ (2 : Nat) =
      pomRealQWeight q * pomRealQDominantRoot q + pomRealQWeight q := by
  have hdisc_nonneg :
      0 ≤ pomRealQWeight q ^ (2 : Nat) + 4 * pomRealQWeight q := by
    nlinarith [sq_nonneg (pomRealQWeight q), pomRealQWeight_nonneg hq]
  unfold pomRealQDominantRoot
  nlinarith [Real.sq_sqrt hdisc_nonneg]

private lemma pomRealQDominantRoot_ge_weight {q : ℝ} (hq : 0 < q) :
    pomRealQWeight q ≤ pomRealQDominantRoot q := by
  have hw_nonneg : 0 ≤ pomRealQWeight q := pomRealQWeight_nonneg hq
  have hdisc_nonneg :
      0 ≤ pomRealQWeight q ^ (2 : Nat) + 4 * pomRealQWeight q := by
    nlinarith [sq_nonneg (pomRealQWeight q), hw_nonneg]
  have hsqrt_nonneg :
      0 ≤ Real.sqrt (pomRealQWeight q ^ (2 : Nat) + 4 * pomRealQWeight q) := by
    positivity
  have hsqrt_ge :
      pomRealQWeight q ≤
        Real.sqrt (pomRealQWeight q ^ (2 : Nat) + 4 * pomRealQWeight q) := by
    nlinarith [Real.sq_sqrt hdisc_nonneg, hw_nonneg, hsqrt_nonneg]
  unfold pomRealQDominantRoot
  nlinarith

private lemma pomRealQDominantRoot_pos {q : ℝ} (hq : 0 < q) : 0 < pomRealQDominantRoot q := by
  exact lt_of_lt_of_le (pomRealQWeight_pos hq) (pomRealQDominantRoot_ge_weight hq)

private lemma pomRealQDominantRoot_gt_one {q : ℝ} (hq : 0 < q) : 1 < pomRealQDominantRoot q := by
  have hw : 1 < pomRealQWeight q := by
    unfold pomRealQWeight
    linarith
  exact lt_of_lt_of_le hw (pomRealQDominantRoot_ge_weight hq)

private lemma pomRealQRoot_pos {q : ℝ} (hq : 0 < q) : 0 < pomRealQRoot q := by
  unfold pomRealQRoot
  exact inv_pos.mpr (pomRealQDominantRoot_pos hq)

private lemma pomRealQRoot_lt_one {q : ℝ} (hq : 0 < q) : pomRealQRoot q < 1 := by
  simpa [pomRealQRoot] using inv_lt_one_of_one_lt₀ (pomRealQDominantRoot_gt_one hq)

private lemma pomRealQSeries_root_eq_one {q : ℝ} (hq : 0 < q) :
    pomRealQSeries q (pomRealQRoot q) = 1 := by
  have hdom_sq := pomRealQDominantRoot_sq hq
  have hdom_ne : pomRealQDominantRoot q ≠ 0 := ne_of_gt (pomRealQDominantRoot_pos hq)
  have hmain :
      pomRealQWeight q * (pomRealQDominantRoot q)⁻¹ +
          pomRealQWeight q * ((pomRealQDominantRoot q)⁻¹) ^ (2 : Nat) = 1 := by
    field_simp [hdom_ne]
    nlinarith [hdom_sq]
  simpa [pomRealQSeries, pomRealQRoot] using hmain

private lemma pomRealQRoot_unique {q ρ : ℝ} (hq : 0 < q) (hρ : 0 < ρ)
    (hEq : pomRealQSeries q ρ = 1) : ρ = pomRealQRoot q := by
  have hwpos : 0 < pomRealQWeight q := pomRealQWeight_pos hq
  have hwne : pomRealQWeight q ≠ 0 := ne_of_gt hwpos
  have hρquad : ρ ^ (2 : Nat) + ρ = (pomRealQWeight q)⁻¹ := by
    have hEq' : pomRealQWeight q * ρ ^ (2 : Nat) + pomRealQWeight q * ρ = 1 := by
      simpa [pomRealQSeries, mul_add, add_comm, add_left_comm, add_assoc] using hEq
    field_simp [hwne]
    nlinarith [hEq']
  have hrootquad : pomRealQRoot q ^ (2 : Nat) + pomRealQRoot q = (pomRealQWeight q)⁻¹ := by
    have hEqRoot := pomRealQSeries_root_eq_one hq
    have hEq' : pomRealQWeight q * (pomRealQRoot q) ^ (2 : Nat) + pomRealQWeight q * pomRealQRoot q = 1 := by
      simpa [pomRealQSeries, mul_add, add_comm, add_left_comm, add_assoc] using hEqRoot
    field_simp [hwne]
    nlinarith [hEq']
  have hprod : (ρ - pomRealQRoot q) * (ρ + pomRealQRoot q + 1) = 0 := by
    nlinarith [hρquad, hrootquad]
  have hsum_ne : ρ + pomRealQRoot q + 1 ≠ 0 := by
    have hpos : 0 < ρ + pomRealQRoot q + 1 := by
      have hroot_pos := pomRealQRoot_pos hq
      positivity
    linarith
  rcases mul_eq_zero.mp hprod with hzero | hzero
  · linarith
  · exact False.elim (hsum_ne hzero)

private lemma pomRealQDominantRoot_strict_mono {q₁ q₂ : ℝ} (hq₁ : 0 < q₁) (hq₂ : q₁ < q₂) :
    pomRealQDominantRoot q₁ < pomRealQDominantRoot q₂ := by
  have hw : pomRealQWeight q₁ < pomRealQWeight q₂ := by
    unfold pomRealQWeight
    linarith
  have hw1_nonneg : 0 ≤ pomRealQWeight q₁ := (pomRealQWeight_pos hq₁).le
  have hw2_pos : 0 < pomRealQWeight q₂ := pomRealQWeight_pos (lt_trans hq₁ hq₂)
  have hw2_nonneg : 0 ≤ pomRealQWeight q₂ := hw2_pos.le
  have hdisc_lt :
      pomRealQWeight q₁ ^ (2 : Nat) + 4 * pomRealQWeight q₁ <
        pomRealQWeight q₂ ^ (2 : Nat) + 4 * pomRealQWeight q₂ := by
    nlinarith [hw, hw1_nonneg, hw2_nonneg]
  have hsqrt_lt :
      Real.sqrt (pomRealQWeight q₁ ^ (2 : Nat) + 4 * pomRealQWeight q₁) <
        Real.sqrt (pomRealQWeight q₂ ^ (2 : Nat) + 4 * pomRealQWeight q₂) := by
    exact Real.sqrt_lt_sqrt (by positivity) hdisc_lt
  unfold pomRealQDominantRoot
  nlinarith

private lemma pomRealQRoot_strict_anti {q₁ q₂ : ℝ} (hq₁ : 0 < q₁) (hq₂ : q₁ < q₂) :
    pomRealQRoot q₂ < pomRealQRoot q₁ := by
  have hdom := pomRealQDominantRoot_strict_mono hq₁ hq₂
  have hdom₁pos : 0 < pomRealQDominantRoot q₁ := pomRealQDominantRoot_pos hq₁
  simpa [pomRealQRoot, one_div] using one_div_lt_one_div_of_lt hdom₁pos hdom

private lemma pomRealQPressure_eq_neg_log_root {q : ℝ} (_hq : 0 < q) :
    pomRealQPressure q = -Real.log (pomRealQRoot q) := by
  unfold pomRealQPressure pomRealQRoot
  rw [Real.log_inv]
  ring

/-- Paper label: `thm:pom-multiplicity-real-q-pressure`.
The real-parameter continuation of the multiplicity-composition two-step hierarchy has a unique
positive root `ρ(q)` of `W_q(ρ) = 1`; at integer `q` it matches the reciprocal moment-hierarchy
Perron root, the root decreases strictly with `q`, and the pressure is `-log ρ(q)`. -/
theorem paper_pom_multiplicity_real_q_pressure : pomMultiplicityRealQPressureStatement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    refine ⟨pomRealQRoot_pos hq, pomRealQRoot_lt_one hq, pomRealQSeries_root_eq_one hq, ?_⟩
    intro ρ hρ hEq
    exact pomRealQRoot_unique hq hρ hEq
  · intro n
    rfl
  · intro q₁ q₂ hq₁ hq₂
    exact pomRealQRoot_strict_anti hq₁ hq₂
  · intro q hq
    exact pomRealQPressure_eq_neg_log_root hq

end

end Omega.POM
