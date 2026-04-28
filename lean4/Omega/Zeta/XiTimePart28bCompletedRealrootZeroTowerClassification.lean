import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Case code for the real parameter in `y + y⁻¹ = S₀`: interior, `+2`, `-2`, or exterior. -/
def xi_time_part28b_completed_realroot_zero_tower_classification_caseCode (S₀ : ℝ) : ℕ :=
  if |S₀| < 2 then 0 else if S₀ = 2 then 1 else if S₀ = -2 then 2 else 3

/-- Algebraic residual of the equation `y + y⁻¹ = S₀`. -/
def xi_time_part28b_completed_realroot_zero_tower_classification_quadraticResidual
    (S₀ y : ℝ) : ℝ :=
  y ^ 2 - S₀ * y + 1

/-- Derivative factor of `y + y⁻¹` with respect to the local coordinate `y`. -/
def xi_time_part28b_completed_realroot_zero_tower_classification_derivativeFactor
    (y : ℝ) : ℝ :=
  1 - 1 / y ^ 2

/-- The logarithmic vertical spacing of the zero combs. -/
def xi_time_part28b_completed_realroot_zero_tower_classification_period (L : ℝ) : ℝ :=
  2 * Real.pi / Real.log L

/-- Multiplicity transfer through `S_L`: noncritical branches keep multiplicity, while
the endpoint branches double it. -/
def xi_time_part28b_completed_realroot_zero_tower_classification_transferredMultiplicity
    (m : ℕ) (derivativeVanishes : Bool) : ℕ :=
  if derivativeVanishes then 2 * m else m

/-- Concrete algebraic classification behind the completed real-root zero towers. -/
def xi_time_part28b_completed_realroot_zero_tower_classification_statement
    (L S₀ : ℝ) : Prop :=
  0 < Real.log L ∧
    0 < xi_time_part28b_completed_realroot_zero_tower_classification_period L ∧
    (|S₀| < 2 →
      xi_time_part28b_completed_realroot_zero_tower_classification_caseCode S₀ = 0) ∧
    (S₀ = 2 →
      xi_time_part28b_completed_realroot_zero_tower_classification_caseCode S₀ = 1) ∧
      (S₀ = -2 →
        xi_time_part28b_completed_realroot_zero_tower_classification_caseCode S₀ = 2) ∧
        (2 < S₀ →
          xi_time_part28b_completed_realroot_zero_tower_classification_caseCode S₀ = 3) ∧
        (S₀ < -2 →
          xi_time_part28b_completed_realroot_zero_tower_classification_caseCode S₀ = 3) ∧
          (∀ S₀ y : ℝ, y ≠ 0 → y + 1 / y = S₀ →
            xi_time_part28b_completed_realroot_zero_tower_classification_quadraticResidual
              S₀ y = 0) ∧
            (∀ y : ℝ, y ≠ 0 → y + 1 / y = 2 →
              y = 1 ∧
                xi_time_part28b_completed_realroot_zero_tower_classification_derivativeFactor
                  y = 0) ∧
              (∀ y : ℝ, y ≠ 0 → y + 1 / y = -2 →
                y = -1 ∧
                  xi_time_part28b_completed_realroot_zero_tower_classification_derivativeFactor
                    y = 0) ∧
                (∀ S₀ y : ℝ, y ≠ 0 → y + 1 / y = S₀ → S₀ ≠ 2 → S₀ ≠ -2 →
                  xi_time_part28b_completed_realroot_zero_tower_classification_derivativeFactor
                    y ≠ 0) ∧
                  (∀ m : ℕ,
                    xi_time_part28b_completed_realroot_zero_tower_classification_transferredMultiplicity
                        m true = 2 * m ∧
                      xi_time_part28b_completed_realroot_zero_tower_classification_transferredMultiplicity
                        m false = m)

lemma xi_time_part28b_completed_realroot_zero_tower_classification_quadraticResidual_eq_zero
    {S₀ y : ℝ} (hy : y ≠ 0) (h : y + 1 / y = S₀) :
    xi_time_part28b_completed_realroot_zero_tower_classification_quadraticResidual S₀ y = 0 := by
  unfold xi_time_part28b_completed_realroot_zero_tower_classification_quadraticResidual
  have hmul : (y + 1 / y) * y = S₀ * y := by rw [h]
  field_simp [hy] at hmul
  nlinarith

lemma xi_time_part28b_completed_realroot_zero_tower_classification_derivative_zero_iff
    {y : ℝ} (hy : y ≠ 0) :
    xi_time_part28b_completed_realroot_zero_tower_classification_derivativeFactor y = 0 ↔
      y = 1 ∨ y = -1 := by
  unfold xi_time_part28b_completed_realroot_zero_tower_classification_derivativeFactor
  constructor
  · intro h
    have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
    field_simp [hy2] at h
    have hfactor : (y - 1) * (y + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · left
      linarith
    · right
      linarith
  · intro h
    rcases h with rfl | rfl <;> norm_num

lemma xi_time_part28b_completed_realroot_zero_tower_classification_endpoint_plus
    {y : ℝ} (hy : y ≠ 0) (h : y + 1 / y = 2) :
    y = 1 ∧
      xi_time_part28b_completed_realroot_zero_tower_classification_derivativeFactor y = 0 := by
  have hquad :=
    xi_time_part28b_completed_realroot_zero_tower_classification_quadraticResidual_eq_zero
      (S₀ := 2) hy h
  unfold xi_time_part28b_completed_realroot_zero_tower_classification_quadraticResidual at hquad
  have hyone : y = 1 := by
    have hsquare : (y - 1) ^ 2 = 0 := by nlinarith
    nlinarith [sq_nonneg (y - 1)]
  subst y
  norm_num [xi_time_part28b_completed_realroot_zero_tower_classification_derivativeFactor]

lemma xi_time_part28b_completed_realroot_zero_tower_classification_endpoint_minus
    {y : ℝ} (hy : y ≠ 0) (h : y + 1 / y = -2) :
    y = -1 ∧
      xi_time_part28b_completed_realroot_zero_tower_classification_derivativeFactor y = 0 := by
  have hquad :=
    xi_time_part28b_completed_realroot_zero_tower_classification_quadraticResidual_eq_zero
      (S₀ := -2) hy h
  unfold xi_time_part28b_completed_realroot_zero_tower_classification_quadraticResidual at hquad
  have hyone : y = -1 := by
    have hsquare : (y + 1) ^ 2 = 0 := by nlinarith
    nlinarith [sq_nonneg (y + 1)]
  subst y
  norm_num [xi_time_part28b_completed_realroot_zero_tower_classification_derivativeFactor]

/-- Paper label: `thm:xi-time-part28b-completed-realroot-zero-tower-classification`. -/
theorem paper_xi_time_part28b_completed_realroot_zero_tower_classification
    (L S₀ : ℝ) (hL : 1 < L) :
    xi_time_part28b_completed_realroot_zero_tower_classification_statement L S₀ := by
  have hlog_pos : 0 < Real.log L := Real.log_pos hL
  have hperiod_pos :
      0 < xi_time_part28b_completed_realroot_zero_tower_classification_period L := by
    unfold xi_time_part28b_completed_realroot_zero_tower_classification_period
    positivity
  refine ⟨hlog_pos, hperiod_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hS₀
    simp [xi_time_part28b_completed_realroot_zero_tower_classification_caseCode, hS₀]
  · intro hS₀
    subst S₀
    norm_num [xi_time_part28b_completed_realroot_zero_tower_classification_caseCode]
  · intro hS₀
    subst S₀
    norm_num [xi_time_part28b_completed_realroot_zero_tower_classification_caseCode]
  · intro hS₀
    unfold xi_time_part28b_completed_realroot_zero_tower_classification_caseCode
    split_ifs with hlt hplus hminus
    · have habs_gt : 2 < |S₀| := by
        rw [abs_of_pos (by linarith)]
        exact hS₀
      linarith
    · subst S₀
      linarith
    · subst S₀
      linarith
    · rfl
  · intro hS₀
    unfold xi_time_part28b_completed_realroot_zero_tower_classification_caseCode
    split_ifs with hlt hplus hminus
    · rw [abs_of_neg (by linarith)] at hlt
      linarith
    · subst S₀
      linarith
    · subst S₀
      linarith
    · rfl
  · intro S₀ y hy h
    exact
      xi_time_part28b_completed_realroot_zero_tower_classification_quadraticResidual_eq_zero
        hy h
  · intro y hy h
    exact xi_time_part28b_completed_realroot_zero_tower_classification_endpoint_plus hy h
  · intro y hy h
    exact xi_time_part28b_completed_realroot_zero_tower_classification_endpoint_minus hy h
  · constructor
    · intro S₀ y hy h hplus hminus hderiv
      have hycases :=
        (xi_time_part28b_completed_realroot_zero_tower_classification_derivative_zero_iff
          hy).1 hderiv
      rcases hycases with rfl | rfl
      · norm_num at h
        exact hplus h.symm
      · norm_num at h
        exact hminus h.symm
    · intro m
      norm_num
        [xi_time_part28b_completed_realroot_zero_tower_classification_transferredMultiplicity]

end

end Omega.Zeta
