import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Tactic
import Omega.Zeta.XiDefectEntropyHyperbolicAreaLaw4pi

namespace Omega.Zeta

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-- The single finite-defect boundary profile. -/
noncomputable def xi_jensen_boundary_potential_finite_defect_explicit_singleProfile
    {ι : Type} (γ δ : ι → ℝ) (m : ι → ℕ) (i : ι) (x : ℝ) : ℝ :=
  (m i : ℝ) * (4 * δ i) / (((x - γ i) ^ 2) + (1 + δ i) ^ 2)

/-- The finite Jensen boundary potential obtained by summing the single-defect profiles. -/
noncomputable def xi_jensen_boundary_potential_finite_defect_explicit_profile
    {ι : Type} [Fintype ι] (γ δ : ι → ℝ) (m : ι → ℕ) (x : ℝ) : ℝ :=
  ∑ i, xi_jensen_boundary_potential_finite_defect_explicit_singleProfile γ δ m i x

lemma xi_jensen_boundary_potential_finite_defect_explicit_singleProfile_eq_cauchy
    {ι : Type} (γ δ : ι → ℝ) (m : ι → ℕ) (i : ι) (hδ : 0 < δ i) :
    xi_jensen_boundary_potential_finite_defect_explicit_singleProfile γ δ m i =
      fun x : ℝ =>
        (4 * Real.pi * ((m i : ℝ) * (δ i / (1 + δ i)))) *
          Probability.cauchyPDFReal (γ i) ⟨1 + δ i, by linarith⟩ x := by
  funext x
  rw [Probability.cauchyPDFReal_def]
  simp [xi_jensen_boundary_potential_finite_defect_explicit_singleProfile, div_eq_mul_inv]
  field_simp [Real.pi_ne_zero, (show (1 + δ i : ℝ) ≠ 0 by linarith)]

lemma xi_jensen_boundary_potential_finite_defect_explicit_singleProfile_integrable
    {ι : Type} (γ δ : ι → ℝ) (m : ι → ℕ) (i : ι) (hδ : 0 < δ i) :
    Integrable (xi_jensen_boundary_potential_finite_defect_explicit_singleProfile γ δ m i) := by
  rw [xi_jensen_boundary_potential_finite_defect_explicit_singleProfile_eq_cauchy γ δ m i hδ]
  exact (Probability.integrable_cauchyPDFReal (γ i) (γ := ⟨1 + δ i, by linarith⟩)).const_mul _

lemma xi_jensen_boundary_potential_finite_defect_explicit_profile_integrable
    {ι : Type} [Fintype ι] [DecidableEq ι] (γ δ : ι → ℝ) (m : ι → ℕ)
    (hδ : ∀ i, 0 < δ i) :
    Integrable (xi_jensen_boundary_potential_finite_defect_explicit_profile γ δ m) := by
  classical
  unfold xi_jensen_boundary_potential_finite_defect_explicit_profile
  refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
  · simp
  · intro i s hi hs
    simpa [hi, Pi.add_apply] using
      (xi_jensen_boundary_potential_finite_defect_explicit_singleProfile_integrable γ δ m i
        (hδ i)).add hs

lemma xi_jensen_boundary_potential_finite_defect_explicit_singleProfile_tendsto_zero
    {ι : Type} (γ δ : ι → ℝ) (m : ι → ℕ) (i : ι) :
    Filter.Tendsto (xi_jensen_boundary_potential_finite_defect_explicit_singleProfile γ δ m i)
      Filter.atTop (nhds 0) := by
  have hsub : Filter.Tendsto (fun x : ℝ => x - γ i) Filter.atTop Filter.atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right Filter.atTop (-γ i) tendsto_id
  have hpow : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop := by
    simpa using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : 1 < (2 : ℕ)) : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop)
  have hsq : Filter.Tendsto (fun x : ℝ => (x - γ i) ^ 2) Filter.atTop Filter.atTop := by
    simpa [Function.comp] using hpow.comp hsub
  have hden :
      Filter.Tendsto (fun x : ℝ => (x - γ i) ^ 2 + (1 + δ i) ^ 2) Filter.atTop Filter.atTop := by
    simpa [add_comm] using
      tendsto_atTop_add_const_right Filter.atTop ((1 + δ i) ^ 2) hsq
  simpa [xi_jensen_boundary_potential_finite_defect_explicit_singleProfile] using
    tendsto_const_nhds.div_atTop hden

/-- Paper label: `thm:xi-jensen-boundary-potential-finite-defect-explicit`. The finite boundary
potential is the explicit finite sum of the single-defect kernels; because the family is finite,
the profile is integrable, its total mass is the summed closed form, and the tail tends to zero. -/
theorem paper_xi_jensen_boundary_potential_finite_defect_explicit
    {ι : Type} [Fintype ι] [DecidableEq ι] (γ δ : ι → ℝ) (m : ι → ℕ)
    (hδ : ∀ i, 0 < δ i) :
    (∀ x : ℝ,
      xi_jensen_boundary_potential_finite_defect_explicit_profile γ δ m x =
        ∑ i, xi_jensen_boundary_potential_finite_defect_explicit_singleProfile γ δ m i x) ∧
      Integrable (xi_jensen_boundary_potential_finite_defect_explicit_profile γ δ m) ∧
      (∫ x, xi_jensen_boundary_potential_finite_defect_explicit_profile γ δ m x =
        4 * Real.pi * ∑ i, (m i : ℝ) * (δ i / (1 + δ i))) ∧
      Filter.Tendsto (xi_jensen_boundary_potential_finite_defect_explicit_profile γ δ m)
        Filter.atTop (nhds 0) := by
  classical
  refine ⟨?_, xi_jensen_boundary_potential_finite_defect_explicit_profile_integrable γ δ m hδ, ?_,
    ?_⟩
  · intro x
    rfl
  · have hmass :=
        paper_xi_defect_entropy_hyperbolic_area_law_4pi (ι := ι) γ δ m hδ
    have hsum :
        ∑ i, ∫ x : ℝ, xi_jensen_boundary_potential_finite_defect_explicit_singleProfile γ δ m i x =
          4 * Real.pi * ∑ i, (m i : ℝ) * (δ i / (1 + δ i)) := by
      have h4pi_ne : (4 * Real.pi : ℝ) ≠ 0 := by positivity
      calc
        ∑ i, ∫ x : ℝ, xi_jensen_boundary_potential_finite_defect_explicit_singleProfile γ δ m i x
            =
              ∑ i,
                ∫ x : ℝ,
                  (m i : ℝ) * (4 * δ i) / (((x - γ i) ^ 2) + (1 + δ i) ^ 2) := by
                simp [xi_jensen_boundary_potential_finite_defect_explicit_singleProfile,
                  mul_left_comm, mul_comm]
        _ 
            = (4 * Real.pi) *
                ((1 / (4 * Real.pi)) *
                  ∑ i,
                    ∫ x : ℝ,
                      (m i : ℝ) * (4 * δ i) / (((x - γ i) ^ 2) + (1 + δ i) ^ 2)) := by
                field_simp [h4pi_ne]
                ring
        _ = (4 * Real.pi) * ∑ i, (m i : ℝ) * (δ i / (1 + δ i)) := by
              rw [← hmass]
        _ = 4 * Real.pi * ∑ i, (m i : ℝ) * (δ i / (1 + δ i)) := by ring
    unfold xi_jensen_boundary_potential_finite_defect_explicit_profile
    rw [MeasureTheory.integral_finset_sum (Finset.univ : Finset ι)]
    · simpa using hsum
    · intro i hi
      exact xi_jensen_boundary_potential_finite_defect_explicit_singleProfile_integrable γ δ m i
        (hδ i)
  · unfold xi_jensen_boundary_potential_finite_defect_explicit_profile
    refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
    · simp
    · intro i s hi hs
      simpa [hi, Pi.add_apply] using
        (xi_jensen_boundary_potential_finite_defect_explicit_singleProfile_tendsto_zero γ δ m i).add
          hs

end

end Omega.Zeta
