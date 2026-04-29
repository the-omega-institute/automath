import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import Omega.Conclusion.CayleyModulusPoissonPrimitive
import Omega.Zeta.XiLogdefectBandpassPoissonRepresentation

namespace Omega.Zeta

noncomputable section

/-- Concrete data for the Poisson-primitive representation of the single log-defect kernel. -/
structure xi_log_defect_potential_poisson_primitive_data where
  γ : ℝ
  δ : ℝ
  hδ0 : 0 < δ
  hδ1 : δ < 1

/-- The translated horizontal coordinate `u = x - γ`. -/
def xi_log_defect_potential_poisson_primitive_u
    (D : xi_log_defect_potential_poisson_primitive_data) (x : ℝ) : ℝ :=
  x - D.γ

/-- The Cayley-modulus form of the log-defect kernel. -/
noncomputable def xi_log_defect_potential_poisson_primitive_cayleyModulus
    (D : xi_log_defect_potential_poisson_primitive_data) (x : ℝ) : ℝ :=
  -Real.log <|
    Real.sqrt
      (((xi_log_defect_potential_poisson_primitive_u D x) ^ 2 + (1 - D.δ) ^ 2) /
        ((xi_log_defect_potential_poisson_primitive_u D x) ^ 2 + (1 + D.δ) ^ 2))

/-- The scale primitive obtained from the Poisson kernel. -/
noncomputable def xi_log_defect_potential_poisson_primitive_primitive
    (D : xi_log_defect_potential_poisson_primitive_data) (x : ℝ) : ℝ :=
  xiLogdefectPoissonPrimitive x D.γ (1 + D.δ) - xiLogdefectPoissonPrimitive x D.γ (1 - D.δ)

/-- The Poisson-smoothed kernel at scale `t`. -/
noncomputable def xi_log_defect_potential_poisson_primitive_smoothed
    (D : xi_log_defect_potential_poisson_primitive_data) (t x : ℝ) : ℝ :=
  xiLogdefectPoissonPrimitive x D.γ (t + 1 + D.δ) -
    xiLogdefectPoissonPrimitive x D.γ (t + 1 - D.δ)

/-- The real Poisson kernel on the line. -/
noncomputable def xi_log_defect_potential_poisson_primitive_poissonKernel (u s : ℝ) : ℝ :=
  s / (Real.pi * (u ^ 2 + s ^ 2))

/-- Package of the primitive identity, the closed-form Poisson smoothing, and the scale
derivative formula. -/
def xi_log_defect_potential_poisson_primitive_data.package
    (D : xi_log_defect_potential_poisson_primitive_data) : Prop :=
  (∀ x,
      xi_log_defect_potential_poisson_primitive_cayleyModulus D x =
        xi_log_defect_potential_poisson_primitive_primitive D x) ∧
    (∀ t, 0 < t → ∀ x,
      xi_log_defect_potential_poisson_primitive_smoothed D t x =
        (1 / 2 : ℝ) *
          Real.log
            (((xi_log_defect_potential_poisson_primitive_u D x) ^ 2 + (t + 1 + D.δ) ^ 2) /
              ((xi_log_defect_potential_poisson_primitive_u D x) ^ 2 + (t + 1 - D.δ) ^ 2))) ∧
    (∀ t, 0 < t → ∀ x,
      HasDerivAt
        (fun s => xi_log_defect_potential_poisson_primitive_smoothed D s x)
        (Real.pi *
          (xi_log_defect_potential_poisson_primitive_poissonKernel
              (xi_log_defect_potential_poisson_primitive_u D x) (t + 1 + D.δ) -
            xi_log_defect_potential_poisson_primitive_poissonKernel
              (xi_log_defect_potential_poisson_primitive_u D x) (t + 1 - D.δ)))
        t)

/-- Paper label: `prop:xi-log-defect-potential-poisson-primitive`. -/
theorem paper_xi_log_defect_potential_poisson_primitive
    (D : xi_log_defect_potential_poisson_primitive_data) : D.package := by
  have hminus : 0 < 1 - D.δ := sub_pos.mpr D.hδ1
  have hplus : 0 < 1 + D.δ := by linarith [D.hδ0]
  refine ⟨?_, ?_, ?_⟩
  · intro x
    calc
      xi_log_defect_potential_poisson_primitive_cayleyModulus D x
          =
            (1 / 2 : ℝ) *
              Real.log
                (((xi_log_defect_potential_poisson_primitive_u D x) ^ 2 + (1 + D.δ) ^ 2) /
                  ((xi_log_defect_potential_poisson_primitive_u D x) ^ 2 + (1 - D.δ) ^ 2)) := by
              simpa [xi_log_defect_potential_poisson_primitive_cayleyModulus,
                xi_log_defect_potential_poisson_primitive_u] using
                Omega.Conclusion.paper_conclusion_cayley_modulus_poisson_primitive
                  (xi_log_defect_potential_poisson_primitive_u D x) D.δ
      _ = xiLogdefectPoissonPrimitive x D.γ (1 + D.δ) -
            xiLogdefectPoissonPrimitive x D.γ (1 - D.δ) := by
            simpa [xiLogdefectBandpassScalar, xi_log_defect_potential_poisson_primitive_u] using
              xiLogdefectBandpassScalar_eq_primitive_difference x D.γ (1 - D.δ) (1 + D.δ)
                hminus hplus
      _ = xi_log_defect_potential_poisson_primitive_primitive D x := by
            rfl
  · intro t ht x
    have hminus_t : 0 < t + 1 - D.δ := by linarith
    have hplus_t : 0 < t + 1 + D.δ := by linarith
    symm
    simpa [xi_log_defect_potential_poisson_primitive_smoothed,
      xiLogdefectBandpassScalar, xi_log_defect_potential_poisson_primitive_u] using
      xiLogdefectBandpassScalar_eq_primitive_difference x D.γ (t + 1 - D.δ) (t + 1 + D.δ)
        hminus_t hplus_t
  · intro t ht x
    let u : ℝ := xi_log_defect_potential_poisson_primitive_u D x
    let gPlus : ℝ → ℝ := fun s => u ^ 2 + (s + 1 + D.δ) ^ 2
    let gMinus : ℝ → ℝ := fun s => u ^ 2 + (s + 1 - D.δ) ^ 2
    have hminus_t : 0 < t + 1 - D.δ := by linarith
    have hplus_t : 0 < t + 1 + D.δ := by linarith
    have hargPlus : HasDerivAt (fun s : ℝ => s + 1 + D.δ) 1 t := by
      simpa [add_assoc] using (hasDerivAt_id t).add_const (1 + D.δ)
    have hargMinus : HasDerivAt (fun s : ℝ => s + 1 - D.δ) 1 t := by
      simpa [sub_eq_add_neg, add_assoc] using (hasDerivAt_id t).add_const (1 - D.δ)
    have hgPlusSq : HasDerivAt (fun s : ℝ => (s + 1 + D.δ) ^ 2) (2 * (t + 1 + D.δ)) t := by
      simpa [pow_two, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hargPlus.pow 2
    have hgMinusSq : HasDerivAt (fun s : ℝ => (s + 1 - D.δ) ^ 2) (2 * (t + 1 - D.δ)) t := by
      simpa [pow_two, sub_eq_add_neg, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
        hargMinus.pow 2
    have hgPlus : HasDerivAt gPlus (2 * (t + 1 + D.δ)) t := by
      dsimp [gPlus]
      simpa using hgPlusSq.const_add (u ^ 2)
    have hgMinus : HasDerivAt gMinus (2 * (t + 1 - D.δ)) t := by
      dsimp [gMinus]
      simpa using hgMinusSq.const_add (u ^ 2)
    have hgPlus_ne : gPlus t ≠ 0 := by
      dsimp [gPlus]
      apply ne_of_gt
      have hsquare : 0 < (t + 1 + D.δ) ^ 2 := sq_pos_of_pos hplus_t
      nlinarith [sq_nonneg u]
    have hgMinus_ne : gMinus t ≠ 0 := by
      dsimp [gMinus]
      apply ne_of_gt
      have hsquare : 0 < (t + 1 - D.δ) ^ 2 := sq_pos_of_pos hminus_t
      nlinarith [sq_nonneg u]
    have hlogPlus :
        HasDerivAt (fun s => Real.log (gPlus s)) ((gPlus t)⁻¹ * (2 * (t + 1 + D.δ))) t := by
      simpa [gPlus] using (Real.hasDerivAt_log hgPlus_ne).comp t hgPlus
    have hlogMinus :
        HasDerivAt (fun s => Real.log (gMinus s)) ((gMinus t)⁻¹ * (2 * (t + 1 - D.δ))) t := by
      simpa [gMinus] using (Real.hasDerivAt_log hgMinus_ne).comp t hgMinus
    have hmain :
        HasDerivAt
          (fun s =>
            (1 / 2 : ℝ) * Real.log (gPlus s) - (1 / 2 : ℝ) * Real.log (gMinus s))
          ((1 / 2 : ℝ) * ((gPlus t)⁻¹ * (2 * (t + 1 + D.δ))) -
            (1 / 2 : ℝ) * ((gMinus t)⁻¹ * (2 * (t + 1 - D.δ))))
          t :=
      (hlogPlus.const_mul (1 / 2 : ℝ)).sub (hlogMinus.const_mul (1 / 2 : ℝ))
    have htarget :
        (1 / 2 : ℝ) * ((gPlus t)⁻¹ * (2 * (t + 1 + D.δ))) -
          (1 / 2 : ℝ) * ((gMinus t)⁻¹ * (2 * (t + 1 - D.δ))) =
            Real.pi *
              (xi_log_defect_potential_poisson_primitive_poissonKernel u (t + 1 + D.δ) -
                xi_log_defect_potential_poisson_primitive_poissonKernel u (t + 1 - D.δ)) := by
      have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
      dsimp [gPlus, gMinus, xi_log_defect_potential_poisson_primitive_poissonKernel]
      field_simp [hpi, hgPlus_ne, hgMinus_ne]
    have hmain' :
        HasDerivAt
          (fun s => xi_log_defect_potential_poisson_primitive_smoothed D s x)
          ((1 / 2 : ℝ) * ((gPlus t)⁻¹ * (2 * (t + 1 + D.δ))) -
            (1 / 2 : ℝ) * ((gMinus t)⁻¹ * (2 * (t + 1 - D.δ))))
          t := by
      simpa [xi_log_defect_potential_poisson_primitive_smoothed, xiLogdefectPoissonPrimitive,
        gPlus, gMinus, u] using hmain
    exact htarget ▸ (by simpa [u] using hmain')

end

end Omega.Zeta
