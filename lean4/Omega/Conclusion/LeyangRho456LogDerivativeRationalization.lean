import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import Omega.Conclusion.LeyangRho456WallPotentialIdentities

namespace Omega.Conclusion

noncomputable section

/-- The fourth-wall log absolute cyclotomic factor. -/
def conclusion_leyang_rho456_log_derivative_rationalization_wall4 (u : ℝ) : ℝ :=
  Real.log |u ^ 4 - 1|

/-- The sixth-wall log absolute cyclotomic factor. -/
def conclusion_leyang_rho456_log_derivative_rationalization_wall6 (u : ℝ) : ℝ :=
  Real.log |u ^ 6 - 1|

/-- The normalized `rho6 - 5/6 rho5` wall combination. -/
def conclusion_leyang_rho456_log_derivative_rationalization_rho6_normalized
    (u : ℝ) : ℝ :=
  (1 / 24) * conclusion_leyang_rho456_log_derivative_rationalization_wall4 u

/-- The normalized `rho4 - 5/4 rho5` wall combination. -/
def conclusion_leyang_rho456_log_derivative_rationalization_rho4_normalized
    (u : ℝ) : ℝ :=
  -(1 / 24) * conclusion_leyang_rho456_log_derivative_rationalization_wall6 u

lemma conclusion_leyang_rho456_log_derivative_rationalization_pow4_sub_one_ne
    {u : ℝ} (hu_pos : 0 < u) (hu_ne_one : u ≠ 1) :
    u ^ 4 - 1 ≠ 0 := by
  intro h
  have hpow : u ^ 4 = 1 := sub_eq_zero.mp h
  exact hu_ne_one ((pow_eq_one_iff_of_nonneg hu_pos.le (by norm_num : (4 : ℕ) ≠ 0)).1 hpow)

lemma conclusion_leyang_rho456_log_derivative_rationalization_pow6_sub_one_ne
    {u : ℝ} (hu_pos : 0 < u) (hu_ne_one : u ≠ 1) :
    u ^ 6 - 1 ≠ 0 := by
  intro h
  have hpow : u ^ 6 = 1 := sub_eq_zero.mp h
  exact hu_ne_one ((pow_eq_one_iff_of_nonneg hu_pos.le (by norm_num : (6 : ℕ) ≠ 0)).1 hpow)

lemma conclusion_leyang_rho456_log_derivative_rationalization_wall4_hasDerivAt
    {u : ℝ} (hu_pos : 0 < u) (hu_ne_one : u ≠ 1) :
    HasDerivAt conclusion_leyang_rho456_log_derivative_rationalization_wall4
      (4 * u ^ 3 / (u ^ 4 - 1)) u := by
  have hne := conclusion_leyang_rho456_log_derivative_rationalization_pow4_sub_one_ne
    hu_pos hu_ne_one
  have hbase :
      HasDerivAt (fun x : ℝ => x ^ 4 - 1) (4 * u ^ 3) u := by
    simpa using ((hasDerivAt_id u).pow 4).sub_const (1 : ℝ)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have habs :
        HasDerivAt (fun x : ℝ => |x ^ 4 - 1|) (-(4 * u ^ 3)) u := by
      simpa using (hbase.hasFDerivAt.abs_of_neg hneg).hasDerivAt
    have hlog := habs.log (abs_ne_zero.mpr hne)
    change HasDerivAt (fun u : ℝ => Real.log |u ^ 4 - 1|)
      (4 * u ^ 3 / (u ^ 4 - 1)) u
    convert hlog using 1
    rw [abs_of_neg hneg]
    have hden_left : -1 + u ^ 4 ≠ 0 := by
      intro hzero
      exact hne (by linarith)
    have hden_right : 1 - u ^ 4 ≠ 0 := by
      intro hzero
      exact hne (by linarith)
    field_simp [hden_left, hden_right]
  · have habs :
        HasDerivAt (fun x : ℝ => |x ^ 4 - 1|) (4 * u ^ 3) u := by
      simpa using (hbase.hasFDerivAt.abs_of_pos hpos).hasDerivAt
    have hlog := habs.log (abs_ne_zero.mpr hne)
    change HasDerivAt (fun u : ℝ => Real.log |u ^ 4 - 1|)
      (4 * u ^ 3 / (u ^ 4 - 1)) u
    simpa [abs_of_pos hpos] using hlog

lemma conclusion_leyang_rho456_log_derivative_rationalization_wall6_hasDerivAt
    {u : ℝ} (hu_pos : 0 < u) (hu_ne_one : u ≠ 1) :
    HasDerivAt conclusion_leyang_rho456_log_derivative_rationalization_wall6
      (6 * u ^ 5 / (u ^ 6 - 1)) u := by
  have hne := conclusion_leyang_rho456_log_derivative_rationalization_pow6_sub_one_ne
    hu_pos hu_ne_one
  have hbase :
      HasDerivAt (fun x : ℝ => x ^ 6 - 1) (6 * u ^ 5) u := by
    simpa using ((hasDerivAt_id u).pow 6).sub_const (1 : ℝ)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have habs :
        HasDerivAt (fun x : ℝ => |x ^ 6 - 1|) (-(6 * u ^ 5)) u := by
      simpa using (hbase.hasFDerivAt.abs_of_neg hneg).hasDerivAt
    have hlog := habs.log (abs_ne_zero.mpr hne)
    change HasDerivAt (fun u : ℝ => Real.log |u ^ 6 - 1|)
      (6 * u ^ 5 / (u ^ 6 - 1)) u
    convert hlog using 1
    rw [abs_of_neg hneg]
    have hden_left : -1 + u ^ 6 ≠ 0 := by
      intro hzero
      exact hne (by linarith)
    have hden_right : 1 - u ^ 6 ≠ 0 := by
      intro hzero
      exact hne (by linarith)
    field_simp [hden_left, hden_right]
  · have habs :
        HasDerivAt (fun x : ℝ => |x ^ 6 - 1|) (6 * u ^ 5) u := by
      simpa using (hbase.hasFDerivAt.abs_of_pos hpos).hasDerivAt
    have hlog := habs.log (abs_ne_zero.mpr hne)
    change HasDerivAt (fun u : ℝ => Real.log |u ^ 6 - 1|)
      (6 * u ^ 5 / (u ^ 6 - 1)) u
    simpa [abs_of_pos hpos] using hlog

/-- Concrete statement for rationalized log-derivative slopes after `rho5` normalization. -/
def conclusion_leyang_rho456_log_derivative_rationalization_statement : Prop :=
  (∀ u : ℝ,
    conclusion_leyang_rho456_log_derivative_rationalization_rho6_normalized u =
        (1 / 24) * conclusion_leyang_rho456_log_derivative_rationalization_wall4 u ∧
      conclusion_leyang_rho456_log_derivative_rationalization_rho4_normalized u =
        -(1 / 24) * conclusion_leyang_rho456_log_derivative_rationalization_wall6 u) ∧
  ∀ u : ℝ, 0 < u → u ≠ 1 →
    HasDerivAt conclusion_leyang_rho456_log_derivative_rationalization_rho6_normalized
        ((1 / 24) * (4 * u ^ 3 / (u ^ 4 - 1))) u ∧
      24 * u * ((1 / 24) * (4 * u ^ 3 / (u ^ 4 - 1))) =
        4 * u ^ 4 / (u ^ 4 - 1) ∧
      HasDerivAt conclusion_leyang_rho456_log_derivative_rationalization_rho4_normalized
        (-(1 / 24) * (6 * u ^ 5 / (u ^ 6 - 1))) u ∧
      24 * u * (-(1 / 24) * (6 * u ^ 5 / (u ^ 6 - 1))) =
        -(6 * u ^ 6 / (u ^ 6 - 1))

/-- Paper label: `cor:conclusion-leyang-rho456-log-derivative-rationalization`. -/
theorem paper_conclusion_leyang_rho456_log_derivative_rationalization :
    conclusion_leyang_rho456_log_derivative_rationalization_statement := by
  refine ⟨?_, ?_⟩
  · intro u
    have hwall :=
      paper_conclusion_leyang_rho456_wall_potential_identities
        (conclusion_leyang_rho456_log_derivative_rationalization_rho4_normalized u) 0
        (conclusion_leyang_rho456_log_derivative_rationalization_rho6_normalized u)
        (conclusion_leyang_rho456_log_derivative_rationalization_wall4 u)
        (conclusion_leyang_rho456_log_derivative_rationalization_wall6 u)
        (by
          unfold conclusion_leyang_rho456_log_derivative_rationalization_rho6_normalized
          ring)
        (by
          unfold conclusion_leyang_rho456_log_derivative_rationalization_rho4_normalized
          ring)
    exact ⟨by simpa using hwall.1, by simpa using hwall.2⟩
  · intro u hu_pos hu_ne_one
    have h4 :=
      conclusion_leyang_rho456_log_derivative_rationalization_wall4_hasDerivAt
        hu_pos hu_ne_one
    have h6 :=
      conclusion_leyang_rho456_log_derivative_rationalization_wall6_hasDerivAt
        hu_pos hu_ne_one
    have h4norm :
        HasDerivAt conclusion_leyang_rho456_log_derivative_rationalization_rho6_normalized
          ((1 / 24) * (4 * u ^ 3 / (u ^ 4 - 1))) u := by
      change HasDerivAt
        (fun y : ℝ =>
          (1 / 24) * conclusion_leyang_rho456_log_derivative_rationalization_wall4 y)
        ((1 / 24) * (4 * u ^ 3 / (u ^ 4 - 1))) u
      exact h4.const_mul (1 / 24)
    have h6norm :
        HasDerivAt conclusion_leyang_rho456_log_derivative_rationalization_rho4_normalized
          (-(1 / 24) * (6 * u ^ 5 / (u ^ 6 - 1))) u := by
      change HasDerivAt
        (fun y : ℝ =>
          -(1 / 24) * conclusion_leyang_rho456_log_derivative_rationalization_wall6 y)
        (-(1 / 24) * (6 * u ^ 5 / (u ^ 6 - 1))) u
      exact h6.const_mul (-(1 / 24))
    refine ⟨h4norm, ?_, h6norm, ?_⟩
    · field_simp [
        conclusion_leyang_rho456_log_derivative_rationalization_pow4_sub_one_ne
          hu_pos hu_ne_one]
    · field_simp [
        conclusion_leyang_rho456_log_derivative_rationalization_pow6_sub_one_ne
          hu_pos hu_ne_one]

end

end Omega.Conclusion
