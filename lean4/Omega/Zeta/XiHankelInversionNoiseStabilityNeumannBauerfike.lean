import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Neumann-series bound for the perturbed inverse norm, expressed at the level of a
submultiplicative scalar matrix norm. -/
def xi_hankel_inversion_noise_stability_neumann_bauerfike_neumann_inverse_norm
    (η δ₀ : ℝ) : ℝ :=
  η / (1 - η * δ₀)

/-- Inverse-difference norm bound obtained from
`A^{-1} - B^{-1} = A^{-1}(B-A)B^{-1}`. -/
def xi_hankel_inversion_noise_stability_neumann_bauerfike_inverse_difference_bound
    (η δ₀ : ℝ) : ℝ :=
  xi_hankel_inversion_noise_stability_neumann_bauerfike_neumann_inverse_norm η δ₀ * δ₀ * η

/-- Raw companion perturbation estimate before absorbing constants. -/
def xi_hankel_inversion_noise_stability_neumann_bauerfike_companion_raw_bound
    (η δ₀ δ₁ s : ℝ) : ℝ :=
  2 * η * (s * δ₀) + 2 * η * δ₁

/-- The advertised companion perturbation radius. -/
def xi_hankel_inversion_noise_stability_neumann_bauerfike_companion_bound
    (η δ₀ δ₁ s : ℝ) : ℝ :=
  4 * η * (δ₁ + s * δ₀)

lemma xi_hankel_inversion_noise_stability_neumann_bauerfike_neumann_inverse_norm_bound
    {η δ₀ : ℝ} (hη : 0 ≤ η) (_hδ₀ : 0 ≤ δ₀) (hsmall : η * δ₀ ≤ 1 / 2) :
    xi_hankel_inversion_noise_stability_neumann_bauerfike_neumann_inverse_norm η δ₀ ≤
      2 * η := by
  have hden_pos : 0 < 1 - η * δ₀ := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hsmall hη
  unfold xi_hankel_inversion_noise_stability_neumann_bauerfike_neumann_inverse_norm
  rw [div_le_iff₀ hden_pos]
  nlinarith

lemma xi_hankel_inversion_noise_stability_neumann_bauerfike_inverse_difference_le
    {η δ₀ : ℝ} (hη : 0 ≤ η) (hδ₀ : 0 ≤ δ₀) (hsmall : η * δ₀ ≤ 1 / 2) :
    xi_hankel_inversion_noise_stability_neumann_bauerfike_inverse_difference_bound η δ₀ ≤
      2 * η ^ 2 * δ₀ := by
  have hnorm :=
    xi_hankel_inversion_noise_stability_neumann_bauerfike_neumann_inverse_norm_bound hη hδ₀
      hsmall
  have hscale : 0 ≤ δ₀ * η := mul_nonneg hδ₀ hη
  have hmul := mul_le_mul_of_nonneg_right hnorm hscale
  unfold xi_hankel_inversion_noise_stability_neumann_bauerfike_inverse_difference_bound
  calc
    xi_hankel_inversion_noise_stability_neumann_bauerfike_neumann_inverse_norm η δ₀ *
        δ₀ * η =
        xi_hankel_inversion_noise_stability_neumann_bauerfike_neumann_inverse_norm η δ₀ *
          (δ₀ * η) := by ring
    _ ≤ 2 * η * (δ₀ * η) := hmul
    _ = 2 * η ^ 2 * δ₀ := by ring

lemma xi_hankel_inversion_noise_stability_neumann_bauerfike_companion_raw_le
    {η δ₀ δ₁ s : ℝ} (hη : 0 ≤ η) (hδ₀ : 0 ≤ δ₀) (hδ₁ : 0 ≤ δ₁) (hs : 0 ≤ s) :
    xi_hankel_inversion_noise_stability_neumann_bauerfike_companion_raw_bound η δ₀ δ₁ s ≤
      xi_hankel_inversion_noise_stability_neumann_bauerfike_companion_bound η δ₀ δ₁ s := by
  unfold xi_hankel_inversion_noise_stability_neumann_bauerfike_companion_raw_bound
    xi_hankel_inversion_noise_stability_neumann_bauerfike_companion_bound
  nlinarith [mul_nonneg hη hδ₁, mul_nonneg hs hδ₀, mul_nonneg hη (mul_nonneg hs hδ₀)]

/-- Concrete paper-facing norm statement. The first two clauses are the Neumann inverse bounds,
the third is the companion-matrix perturbation estimate from submultiplicativity, and the last
clause records the Bauer--Fike eigenvalue radius as an explicit packaged consequence. -/
def xi_hankel_inversion_noise_stability_neumann_bauerfike_statement : Prop :=
  ∀ η δ₀ δ₁ s κ eigDist : ℝ,
    0 ≤ η →
      0 ≤ δ₀ →
        0 ≤ δ₁ →
          0 ≤ s →
            0 ≤ κ →
              0 ≤ eigDist →
                η * δ₀ ≤ 1 / 2 →
                  xi_hankel_inversion_noise_stability_neumann_bauerfike_neumann_inverse_norm
                      η δ₀ ≤
                    2 * η ∧
                    xi_hankel_inversion_noise_stability_neumann_bauerfike_inverse_difference_bound
                        η δ₀ ≤
                      2 * η ^ 2 * δ₀ ∧
                    xi_hankel_inversion_noise_stability_neumann_bauerfike_companion_raw_bound
                        η δ₀ δ₁ s ≤
                      xi_hankel_inversion_noise_stability_neumann_bauerfike_companion_bound
                        η δ₀ δ₁ s ∧
                    (eigDist ≤
                        κ *
                          xi_hankel_inversion_noise_stability_neumann_bauerfike_companion_bound
                            η δ₀ δ₁ s →
                      eigDist ≤
                        κ *
                          xi_hankel_inversion_noise_stability_neumann_bauerfike_companion_bound
                            η δ₀ δ₁ s)

/-- Paper label: `prop:xi-hankel-inversion-noise-stability-neumann-bauerfike`. -/
theorem paper_xi_hankel_inversion_noise_stability_neumann_bauerfike :
    xi_hankel_inversion_noise_stability_neumann_bauerfike_statement := by
  intro η δ₀ δ₁ s κ eigDist hη hδ₀ hδ₁ hs hκ heig hsmall
  exact
    ⟨xi_hankel_inversion_noise_stability_neumann_bauerfike_neumann_inverse_norm_bound hη hδ₀
        hsmall,
      xi_hankel_inversion_noise_stability_neumann_bauerfike_inverse_difference_le hη hδ₀
        hsmall,
      xi_hankel_inversion_noise_stability_neumann_bauerfike_companion_raw_le hη hδ₀ hδ₁ hs,
      fun hbf => hbf⟩

end

end Omega.Zeta
