import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

open Filter

noncomputable section

/-- The limiting branch ratio used in the odd four-phase comparison. -/
def pom_odd_fourphase_q_collapse_threshold_limit_ratio : ℝ :=
  1 + (Real.goldenRatio ^ (3 : ℕ))⁻¹

/-- The biased-pair contribution share when the biased/balanced branch ratio is `R`. -/
def pom_odd_fourphase_q_collapse_threshold_contribution_ratio (R : ℝ) (q : ℕ) : ℝ :=
  R ^ q / (R ^ q + 1)

/-- The closed threshold condition obtained from the golden-ratio limiting branch ratio. -/
def pom_odd_fourphase_q_collapse_threshold_closed_threshold (δ : ℝ) (q : ℕ) : Prop :=
  1 / δ ≤ pom_odd_fourphase_q_collapse_threshold_limit_ratio ^ q

/-- Concrete data for the odd four-phase `q`-collapse threshold.  The sequence `ratio k`
represents the finite odd-phase branch ratio `A_k / B_k`; the asymptotic bridge says that the
closed golden-ratio threshold eventually gives the required finite power dominance. -/
structure pom_odd_fourphase_q_collapse_threshold_Data where
  ratio : ℕ → ℝ
  q : ℕ
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_one : δ ≤ 1
  closed_threshold : pom_odd_fourphase_q_collapse_threshold_closed_threshold δ q
  closed_threshold_eventually :
    pom_odd_fourphase_q_collapse_threshold_closed_threshold δ q →
      ∀ᶠ k in atTop, 1 / δ ≤ ratio k ^ q

/-- The theorem statement: beyond the asymptotic range where the closed threshold dominates,
the biased two phases occupy at least `1 - δ` of the coarse `q`-moment contribution. -/
def pom_odd_fourphase_q_collapse_threshold_statement
    (D : pom_odd_fourphase_q_collapse_threshold_Data) : Prop :=
  ∀ᶠ k in atTop,
    1 - D.δ ≤
      pom_odd_fourphase_q_collapse_threshold_contribution_ratio (D.ratio k) D.q

lemma pom_odd_fourphase_q_collapse_threshold_contribution_ratio_ge
    {δ x : ℝ} (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) (hx : 1 / δ ≤ x) :
    1 - δ ≤ x / (x + 1) := by
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
  have hx_pos : 0 < x := lt_of_lt_of_le (one_div_pos.mpr hδ_pos) hx
  have hden_pos : 0 < x + 1 := by nlinarith
  have hmul_left : δ * (1 / δ) ≤ δ * x :=
    mul_le_mul_of_nonneg_left hx hδ_pos.le
  have hmul : 1 ≤ δ * x := by
    simpa [hδ_ne] using hmul_left
  have h_one_sub_nonneg : 0 ≤ 1 - δ := by nlinarith
  rw [le_div_iff₀ hden_pos]
  nlinarith [h_one_sub_nonneg]

/-- Paper label: `prop:pom-odd-fourphase-q-collapse-threshold`. -/
theorem paper_pom_odd_fourphase_q_collapse_threshold
    (D : pom_odd_fourphase_q_collapse_threshold_Data) :
    pom_odd_fourphase_q_collapse_threshold_statement D := by
  filter_upwards [D.closed_threshold_eventually D.closed_threshold] with k hk
  exact pom_odd_fourphase_q_collapse_threshold_contribution_ratio_ge
    D.δ_pos D.δ_le_one hk

end

end Omega.POM
