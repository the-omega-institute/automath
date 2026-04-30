import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

namespace Omega.Conclusion

open Polynomial

/-- The odd-layer mode encoded by the finite-window polynomial.  The shift by `3` keeps the
normalizing point `1` away from all recorded roots. -/
def conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_mode (r : ℕ) : ℚ :=
  (2 * r + 3 : ℚ)

/-- Recursive product polynomial for the first `R` odd layers. -/
noncomputable def conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_productPolynomial :
    ℕ → Polynomial ℚ
  | 0 => 1
  | R + 1 =>
      conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_productPolynomial R *
        (X - C (conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_mode R))

lemma conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_eval_one
    (R : ℕ) :
    (conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_productPolynomial R).eval 1 =
      ∏ r ∈ Finset.range R,
        (1 - conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_mode r) := by
  induction R with
  | zero =>
      simp [conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_productPolynomial]
  | succ R ih =>
      simp [conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_productPolynomial, ih,
        Finset.prod_range_succ]

lemma conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_root_cancel
    (R r : ℕ) (hr : r < R) :
    (conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_productPolynomial R).eval
      (conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_mode r) = 0 := by
  induction R generalizing r with
  | zero =>
      omega
  | succ R ih =>
      rw [conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_productPolynomial]
      by_cases hprev : r < R
      · simp [ih r hprev]
      · have hr_eq : r = R := by omega
        subst r
        simp

lemma conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_factor_ne_zero
    (r : ℕ) :
    1 - conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_mode r ≠ 0 := by
  unfold conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_mode
  have hpos : (0 : ℚ) < 2 * (r : ℚ) + 2 := by positivity
  linarith

lemma conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_eval_one_ne_zero
    (R : ℕ) :
    (∏ r ∈ Finset.range R,
      (1 - conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_mode r)) ≠ 0 := by
  induction R with
  | zero =>
      simp
  | succ R ih =>
      simp [Finset.prod_range_succ, ih,
        conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_factor_ne_zero]

/-- The normalized finite-window annihilator. -/
noncomputable def conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_normalizedPolynomial
    (R : ℕ) : Polynomial ℚ :=
  C ((∏ r ∈ Finset.range R,
    (1 - conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_mode r))⁻¹) *
      conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_productPolynomial R

lemma conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_normalized_eval_one
    (R : ℕ) :
    (conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_normalizedPolynomial R).eval 1 =
      1 := by
  rw [conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_normalizedPolynomial, eval_mul,
    eval_C, conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_eval_one]
  have hprod :=
    conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_eval_one_ne_zero R
  field_simp [hprod]

lemma conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_normalized_root_cancel
    (R r : ℕ) (hr : r < R) :
    (conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_normalizedPolynomial R).eval
      (conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_mode r) = 0 := by
  rw [conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_normalizedPolynomial, eval_mul]
  simp [conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_root_cancel R r hr]

/-- Concrete finite-window annihilation and shifted-mode package. -/
def conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_statement (R : ℕ) : Prop :=
  (conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_normalizedPolynomial R).eval 1 = 1 ∧
    (∀ r : ℕ, r < R →
      (conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_normalizedPolynomial R).eval
        (conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_mode r) = 0) ∧
      (∀ shiftedMode : ℕ → ℚ,
        (∀ r : ℕ, r < R →
          shiftedMode r = conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_mode r) →
          ∀ r : ℕ, r < R →
            (conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_normalizedPolynomial R).eval
              (shiftedMode r) = 0)

/-- Paper label: `thm:conclusion-foldgauge-pi-oddlayer-annihilation-hierarchy`. -/
theorem paper_conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy
    (R : ℕ) :
    conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_statement R := by
  refine ⟨?_, ?_, ?_⟩
  · exact conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_normalized_eval_one R
  · intro r hr
    exact conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_normalized_root_cancel R r hr
  · intro shiftedMode hshift r hr
    rw [hshift r hr]
    exact conclusion_foldgauge_pi_oddlayer_annihilation_hierarchy_normalized_root_cancel R r hr

end Omega.Conclusion
