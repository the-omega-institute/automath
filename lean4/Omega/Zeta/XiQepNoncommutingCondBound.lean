import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- All quadratic eigenvalues are non-real and occur with the displayed conjugate partner. -/
def xi_qep_noncommuting_cond_bound_all_roots_nonreal_conjugate {Root : Type}
    (rootRe rootIm : Root → ℝ) (conjugateRoot : Root → Root) : Prop :=
  ∀ r : Root,
    rootIm r ≠ 0 ∧ rootRe (conjugateRoot r) = rootRe r ∧
      rootIm (conjugateRoot r) = -rootIm r

/-- Lower endpoint of the Rayleigh-quotient strip. -/
def xi_qep_noncommuting_cond_bound_stripLower (lambdaMin logL : ℝ) : ℝ :=
  1 / 2 + Real.log lambdaMin / (2 * logL)

/-- Upper endpoint of the Rayleigh-quotient strip. -/
def xi_qep_noncommuting_cond_bound_stripUpper (lambdaMax logL : ℝ) : ℝ :=
  1 / 2 + Real.log lambdaMax / (2 * logL)

/-- The strip constraint for all zeros represented by the pencil roots. -/
def xi_qep_noncommuting_cond_bound_strip_bound {Root : Type} (rootRe : Root → ℝ)
    (_rayleighQuotient : Root → ℝ) (lambdaMin lambdaMax logL : ℝ) : Prop :=
  ∀ r : Root,
    xi_qep_noncommuting_cond_bound_stripLower lambdaMin logL ≤ rootRe r ∧
      rootRe r ≤ xi_qep_noncommuting_cond_bound_stripUpper lambdaMax logL

/-- Width of the Rayleigh-quotient strip. -/
def xi_qep_noncommuting_cond_bound_stripWidth
    (lambdaMin lambdaMax logL : ℝ) : ℝ :=
  xi_qep_noncommuting_cond_bound_stripUpper lambdaMax logL -
    xi_qep_noncommuting_cond_bound_stripLower lambdaMin logL

/-- The strip width is the logarithmic condition number scaled by `2 log L`. -/
def xi_qep_noncommuting_cond_bound_width_eq
    (lambdaMin lambdaMax kappa logL : ℝ) : Prop :=
  xi_qep_noncommuting_cond_bound_stripWidth lambdaMin lambdaMax logL =
    (1 / (2 * logL)) * Real.log kappa

/-- Reciprocal symmetry of the generalized eigenvalue interval. -/
def xi_qep_noncommuting_cond_bound_spectrum_reciprocal
    (lambdaMin lambdaMax : ℝ) : Prop :=
  lambdaMin * lambdaMax = 1

/-- The reciprocal-spectrum half-width bound about the critical line. -/
def xi_qep_noncommuting_cond_bound_symmetric_half_width_bound {Root : Type}
    (rootRe : Root → ℝ) (_lambdaMin _lambdaMax kappa logL : ℝ) : Prop :=
  ∀ r : Root, |rootRe r - 1 / 2| ≤ (1 / (4 * logL)) * Real.log kappa

/-- Paper label: `thm:xi-qep-noncommuting-cond-bound`. -/
theorem paper_xi_qep_noncommuting_cond_bound {Root : Type}
    (rootRe rootIm : Root → ℝ) (conjugateRoot : Root → Root)
    (rayleighQuotient : Root → ℝ) (lambdaMin lambdaMax kappa logL : ℝ)
    (hlambdaMin_pos : 0 < lambdaMin) (hlambdaMin_le_lambdaMax : lambdaMin ≤ lambdaMax)
    (hlogL_pos : 0 < logL) (hkappa_eq : kappa = lambdaMax / lambdaMin)
    (hrayleigh_bounds :
      ∀ r : Root, lambdaMin ≤ rayleighQuotient r ∧ rayleighQuotient r ≤ lambdaMax)
    (hroot_re_eq :
      ∀ r : Root, rootRe r = 1 / 2 + Real.log (rayleighQuotient r) / (2 * logL))
    (hconjugate_pair :
      ∀ r : Root,
        rootIm r ≠ 0 ∧ rootRe (conjugateRoot r) = rootRe r ∧
          rootIm (conjugateRoot r) = -rootIm r) :
    xi_qep_noncommuting_cond_bound_all_roots_nonreal_conjugate rootRe rootIm
        conjugateRoot ∧
      xi_qep_noncommuting_cond_bound_strip_bound rootRe rayleighQuotient lambdaMin
        lambdaMax logL ∧
      xi_qep_noncommuting_cond_bound_width_eq lambdaMin lambdaMax kappa logL ∧
      (xi_qep_noncommuting_cond_bound_spectrum_reciprocal lambdaMin lambdaMax →
        xi_qep_noncommuting_cond_bound_symmetric_half_width_bound rootRe lambdaMin
          lambdaMax kappa logL) := by
  have hlambdaMax_pos : 0 < lambdaMax :=
    lt_of_lt_of_le hlambdaMin_pos hlambdaMin_le_lambdaMax
  have hlogL2_pos : 0 < 2 * logL := by nlinarith [hlogL_pos]
  have hwidth : xi_qep_noncommuting_cond_bound_width_eq lambdaMin lambdaMax kappa logL := by
    have hlogk :
        Real.log kappa = Real.log lambdaMax - Real.log lambdaMin := by
      rw [hkappa_eq, Real.log_div hlambdaMax_pos.ne' hlambdaMin_pos.ne']
    unfold xi_qep_noncommuting_cond_bound_width_eq
      xi_qep_noncommuting_cond_bound_stripWidth
      xi_qep_noncommuting_cond_bound_stripUpper
      xi_qep_noncommuting_cond_bound_stripLower
    rw [hlogk]
    ring
  have hstrip :
      xi_qep_noncommuting_cond_bound_strip_bound rootRe rayleighQuotient lambdaMin
        lambdaMax logL := by
    intro r
    rcases hrayleigh_bounds r with ⟨hmin, hmax⟩
    have hq_pos : 0 < rayleighQuotient r := lt_of_lt_of_le hlambdaMin_pos hmin
    have hlog_min : Real.log lambdaMin ≤ Real.log (rayleighQuotient r) :=
      Real.log_le_log hlambdaMin_pos hmin
    have hlog_max : Real.log (rayleighQuotient r) ≤ Real.log lambdaMax :=
      Real.log_le_log hq_pos hmax
    rw [hroot_re_eq r]
    constructor
    · unfold xi_qep_noncommuting_cond_bound_stripLower
      simpa [add_comm] using
        add_le_add_left (div_le_div_of_nonneg_right hlog_min hlogL2_pos.le) (1 / 2)
    · unfold xi_qep_noncommuting_cond_bound_stripUpper
      simpa [add_comm] using
        add_le_add_left (div_le_div_of_nonneg_right hlog_max hlogL2_pos.le) (1 / 2)
  refine ⟨hconjugate_pair, hstrip, hwidth, ?_⟩
  intro hrec r
  rcases hrayleigh_bounds r with ⟨hmin, hmax⟩
  have hq_pos : 0 < rayleighQuotient r := lt_of_lt_of_le hlambdaMin_pos hmin
  have hlog_min : Real.log lambdaMin ≤ Real.log (rayleighQuotient r) :=
    Real.log_le_log hlambdaMin_pos hmin
  have hlog_max : Real.log (rayleighQuotient r) ≤ Real.log lambdaMax :=
    Real.log_le_log hq_pos hmax
  have hlog_mul :
      Real.log (lambdaMin * lambdaMax) = Real.log lambdaMin + Real.log lambdaMax := by
    rw [Real.log_mul hlambdaMin_pos.ne' hlambdaMax_pos.ne']
  have hlog_sum_zero : Real.log lambdaMin + Real.log lambdaMax = 0 := by
    have hcongr := congrArg Real.log hrec
    rwa [hlog_mul, Real.log_one] at hcongr
  have hlog_min_neg : Real.log lambdaMin = -Real.log lambdaMax := by
    linarith
  have hlogk :
      Real.log kappa = Real.log lambdaMax - Real.log lambdaMin := by
    rw [hkappa_eq, Real.log_div hlambdaMax_pos.ne' hlambdaMin_pos.ne']
  have hlogk_two : Real.log kappa = 2 * Real.log lambdaMax := by
    rw [hlogk, hlog_min_neg]
    ring
  have habs :
      |Real.log (rayleighQuotient r) / (2 * logL)| ≤
        Real.log lambdaMax / (2 * logL) := by
    rw [abs_le]
    constructor
    · have hleft_base : -Real.log lambdaMax ≤ Real.log (rayleighQuotient r) := by
        simpa [hlog_min_neg] using hlog_min
      have hleft := div_le_div_of_nonneg_right hleft_base hlogL2_pos.le
      simpa [neg_div] using hleft
    · exact div_le_div_of_nonneg_right hlog_max hlogL2_pos.le
  rw [hroot_re_eq r, hlogk_two]
  have hsub :
      1 / 2 + Real.log (rayleighQuotient r) / (2 * logL) - 1 / 2 =
        Real.log (rayleighQuotient r) / (2 * logL) := by
    ring
  have hright :
      (1 / (4 * logL)) * (2 * Real.log lambdaMax) =
        Real.log lambdaMax / (2 * logL) := by
    ring
  rw [hsub, hright]
  exact habs

end

end Omega.Zeta
