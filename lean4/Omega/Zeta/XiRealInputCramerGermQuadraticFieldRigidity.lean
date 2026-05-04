import Mathlib.Tactic
import Omega.Conclusion.RealInput40LocalCramerRightTailMoreCostly
import Omega.Zeta.XiTimePart9wBasicRootUnityErrorExponentToOne

namespace Omega.Zeta

/-- Concrete data marker for the real-input Cramer germ package. -/
abbrev xi_real_input_cramer_germ_quadratic_field_rigidity_data := Unit

noncomputable def xi_real_input_cramer_germ_quadratic_field_rigidity_alpha0 : ℝ :=
  23 / 20 - 7 * Real.sqrt 5 / 20

noncomputable def xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2 : ℝ :=
  xiTimePart9wBasicKappa2

noncomputable def xi_real_input_cramer_germ_quadratic_field_rigidity_kappa3 : ℝ :=
  1416369 / 5000 - 126691 * Real.sqrt 5 / 1000

noncomputable def xi_real_input_cramer_germ_quadratic_field_rigidity_kappa4 : ℝ :=
  xiTimePart9wBasicKappa4

noncomputable def xi_real_input_cramer_germ_quadratic_field_rigidity_sigma : ℝ :=
  Real.sqrt xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2

noncomputable def xi_real_input_cramer_germ_quadratic_field_rigidity_legendreJet
    (δ : ℝ) : ℝ :=
  Omega.Conclusion.realInput40LocalCramerJet
    xi_real_input_cramer_germ_quadratic_field_rigidity_sigma
    xi_real_input_cramer_germ_quadratic_field_rigidity_kappa3
    xi_real_input_cramer_germ_quadratic_field_rigidity_kappa4 δ

namespace xi_real_input_cramer_germ_quadratic_field_rigidity_data

def cumulants_in_qsqrt5 (_D : xi_real_input_cramer_germ_quadratic_field_rigidity_data) :
    Prop :=
  (∃ a b : ℚ,
      xi_real_input_cramer_germ_quadratic_field_rigidity_alpha0 =
        (a : ℝ) + (b : ℝ) * Real.sqrt 5) ∧
    (∃ a b : ℚ,
      xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2 =
        (a : ℝ) + (b : ℝ) * Real.sqrt 5) ∧
    (∃ a b : ℚ,
      xi_real_input_cramer_germ_quadratic_field_rigidity_kappa3 =
        (a : ℝ) + (b : ℝ) * Real.sqrt 5) ∧
    (∃ a b : ℚ,
      xi_real_input_cramer_germ_quadratic_field_rigidity_kappa4 =
        (a : ℝ) + (b : ℝ) * Real.sqrt 5) ∧
    0 < xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2 ∧
    xi_real_input_cramer_germ_quadratic_field_rigidity_kappa3 < 0 ∧
    0 < xi_real_input_cramer_germ_quadratic_field_rigidity_kappa4

def legendre_local_expansion
    (_D : xi_real_input_cramer_germ_quadratic_field_rigidity_data) : Prop :=
  ∀ δ : ℝ,
    xi_real_input_cramer_germ_quadratic_field_rigidity_legendreJet δ =
      δ ^ 2 / (2 * xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2) -
        (xi_real_input_cramer_germ_quadratic_field_rigidity_kappa3 /
            (6 * xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2 ^ 3)) *
          δ ^ 3 +
          ((3 * xi_real_input_cramer_germ_quadratic_field_rigidity_kappa3 ^ 2 -
                xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2 *
                  xi_real_input_cramer_germ_quadratic_field_rigidity_kappa4) /
              (24 * xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2 ^ 5)) *
            δ ^ 4

def right_tail_strictly_more_costly
    (_D : xi_real_input_cramer_germ_quadratic_field_rigidity_data) : Prop :=
  ∀ δ : ℝ,
    0 < δ →
      xi_real_input_cramer_germ_quadratic_field_rigidity_legendreJet (-δ) <
        xi_real_input_cramer_germ_quadratic_field_rigidity_legendreJet δ

end xi_real_input_cramer_germ_quadratic_field_rigidity_data

lemma xi_real_input_cramer_germ_quadratic_field_rigidity_sqrt5_sq :
    (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
  rw [Real.sq_sqrt]
  norm_num

lemma xi_real_input_cramer_germ_quadratic_field_rigidity_sqrt5_lower :
    (559 : ℝ) / 250 < Real.sqrt 5 := by
  have hsq := xi_real_input_cramer_germ_quadratic_field_rigidity_sqrt5_sq
  have hnonneg : 0 ≤ (Real.sqrt 5 : ℝ) := by positivity
  by_contra hnot
  have hle : Real.sqrt 5 ≤ (559 : ℝ) / 250 := le_of_not_gt hnot
  nlinarith

lemma xi_real_input_cramer_germ_quadratic_field_rigidity_sqrt5_upper :
    Real.sqrt 5 < (2236068 : ℝ) / 1000000 := by
  have hsq := xi_real_input_cramer_germ_quadratic_field_rigidity_sqrt5_sq
  have hnonneg : 0 ≤ (Real.sqrt 5 : ℝ) := by positivity
  by_contra hnot
  have hle : (2236068 : ℝ) / 1000000 ≤ Real.sqrt 5 := le_of_not_gt hnot
  nlinarith

lemma xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2_pos :
    0 < xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2 := by
  have hupper := xi_real_input_cramer_germ_quadratic_field_rigidity_sqrt5_upper
  unfold xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2 xiTimePart9wBasicKappa2
  nlinarith

lemma xi_real_input_cramer_germ_quadratic_field_rigidity_kappa3_neg :
    xi_real_input_cramer_germ_quadratic_field_rigidity_kappa3 < 0 := by
  have hlower := xi_real_input_cramer_germ_quadratic_field_rigidity_sqrt5_lower
  unfold xi_real_input_cramer_germ_quadratic_field_rigidity_kappa3
  nlinarith

lemma xi_real_input_cramer_germ_quadratic_field_rigidity_kappa4_pos :
    0 < xi_real_input_cramer_germ_quadratic_field_rigidity_kappa4 := by
  have hupper := xi_real_input_cramer_germ_quadratic_field_rigidity_sqrt5_upper
  unfold xi_real_input_cramer_germ_quadratic_field_rigidity_kappa4 xiTimePart9wBasicKappa4
  nlinarith

lemma xi_real_input_cramer_germ_quadratic_field_rigidity_sigma_pos :
    0 < xi_real_input_cramer_germ_quadratic_field_rigidity_sigma := by
  unfold xi_real_input_cramer_germ_quadratic_field_rigidity_sigma
  exact Real.sqrt_pos.2 xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2_pos

lemma xi_real_input_cramer_germ_quadratic_field_rigidity_cumulants_in_qsqrt5
    (D : xi_real_input_cramer_germ_quadratic_field_rigidity_data) :
    D.cumulants_in_qsqrt5 := by
  refine ⟨?_, ?_, ?_, ?_, xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2_pos,
    xi_real_input_cramer_germ_quadratic_field_rigidity_kappa3_neg,
    xi_real_input_cramer_germ_quadratic_field_rigidity_kappa4_pos⟩
  · refine ⟨(23 : ℚ) / 20, -(7 : ℚ) / 20, ?_⟩
    unfold xi_real_input_cramer_germ_quadratic_field_rigidity_alpha0
    ring_nf
  · refine ⟨(8955 : ℚ) / 1000, -(3983 : ℚ) / 1000, ?_⟩
    unfold xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2 xiTimePart9wBasicKappa2
    ring_nf
  · refine ⟨(1416369 : ℚ) / 5000, -(126691 : ℚ) / 1000, ?_⟩
    unfold xi_real_input_cramer_germ_quadratic_field_rigidity_kappa3
    ring_nf
  · refine ⟨(1354428303 : ℚ) / 100000, -(605718497 : ℚ) / 100000, ?_⟩
    unfold xi_real_input_cramer_germ_quadratic_field_rigidity_kappa4 xiTimePart9wBasicKappa4
    ring_nf

lemma xi_real_input_cramer_germ_quadratic_field_rigidity_legendre_local_expansion
    (D : xi_real_input_cramer_germ_quadratic_field_rigidity_data) :
    D.legendre_local_expansion := by
  intro δ
  have hσ2 :
      xi_real_input_cramer_germ_quadratic_field_rigidity_sigma ^ 2 =
        xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2 := by
    unfold xi_real_input_cramer_germ_quadratic_field_rigidity_sigma
    exact Real.sq_sqrt
      (le_of_lt xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2_pos)
  have hσ6 :
      xi_real_input_cramer_germ_quadratic_field_rigidity_sigma ^ 6 =
        xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2 ^ 3 := by
    calc
      xi_real_input_cramer_germ_quadratic_field_rigidity_sigma ^ 6 =
          (xi_real_input_cramer_germ_quadratic_field_rigidity_sigma ^ 2) ^ 3 := by ring
      _ = xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2 ^ 3 := by rw [hσ2]
  have hσ10 :
      xi_real_input_cramer_germ_quadratic_field_rigidity_sigma ^ 10 =
        xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2 ^ 5 := by
    calc
      xi_real_input_cramer_germ_quadratic_field_rigidity_sigma ^ 10 =
          (xi_real_input_cramer_germ_quadratic_field_rigidity_sigma ^ 2) ^ 5 := by ring
      _ = xi_real_input_cramer_germ_quadratic_field_rigidity_kappa2 ^ 5 := by rw [hσ2]
  unfold xi_real_input_cramer_germ_quadratic_field_rigidity_legendreJet
  unfold Omega.Conclusion.realInput40LocalCramerJet
  rw [hσ2, hσ6, hσ10]

lemma xi_real_input_cramer_germ_quadratic_field_rigidity_right_tail_strictly_more_costly
    (D : xi_real_input_cramer_germ_quadratic_field_rigidity_data) :
    D.right_tail_strictly_more_costly := by
  intro δ hδ
  have hpackage :=
    Omega.Conclusion.paper_conclusion_realinput40_local_cramer_right_tail_more_costly_package
      (σ := xi_real_input_cramer_germ_quadratic_field_rigidity_sigma)
      (κ₃ := xi_real_input_cramer_germ_quadratic_field_rigidity_kappa3)
      (κ₄ := xi_real_input_cramer_germ_quadratic_field_rigidity_kappa4)
      (δ := δ) xi_real_input_cramer_germ_quadratic_field_rigidity_sigma_pos
      xi_real_input_cramer_germ_quadratic_field_rigidity_kappa3_neg hδ
  exact sub_pos.mp hpackage.2

/-- Paper label: `thm:xi-real-input-cramer-germ-quadratic-field-rigidity`. -/
theorem paper_xi_real_input_cramer_germ_quadratic_field_rigidity
    (D : xi_real_input_cramer_germ_quadratic_field_rigidity_data) :
    D.cumulants_in_qsqrt5 ∧ D.legendre_local_expansion ∧
      D.right_tail_strictly_more_costly := by
  exact ⟨xi_real_input_cramer_germ_quadratic_field_rigidity_cumulants_in_qsqrt5 D,
    xi_real_input_cramer_germ_quadratic_field_rigidity_legendre_local_expansion D,
    xi_real_input_cramer_germ_quadratic_field_rigidity_right_tail_strictly_more_costly D⟩

end Omega.Zeta
