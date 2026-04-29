import Omega.Zeta.XiTimePart62dcaHologramBernoulliLqSpectrum
import Omega.Zeta.XiTimePart62dcHologramBernoulliExactDimensional

namespace Omega.Zeta

/-- Uniform Renyi dimension constancy for the label
`cor:xi-time-part62dca-hologram-uniform-monofractal-collapse`. -/
noncomputable def xi_time_part62dca_hologram_uniform_monofractal_collapse_renyi_dimension_constancy
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  (∀ i,
      D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_probability i =
        (D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card : ℝ)⁻¹) →
    ∀ (B spectralBase tau : ℝ) (Z : ℕ → ℝ), 1 < B → Z 0 = 1 →
      (∀ n : ℕ, Z (n + 1) = spectralBase * Z n) →
        tau = -Real.log spectralBase / Real.log B →
          (∀ n : ℕ, Z n = spectralBase ^ n) ∧
            tau = -Real.log spectralBase / Real.log B

/-- Singleton multifractal spectrum claim for the uniform hologram wrapper. -/
noncomputable def xi_time_part62dca_hologram_uniform_monofractal_collapse_singleton_spectrum
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  (∀ i,
      D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_probability i =
        (D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card : ℝ)⁻¹) →
    ∀ n (w : D.addr_prefix n),
      D.ball_mass w =
          ((D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card : ℝ)⁻¹) ^ n ∧
        D.dimension_value = D.entropy / D.log_base

/-- Statement package for
`cor:xi-time-part62dca-hologram-uniform-monofractal-collapse`. -/
noncomputable def xi_time_part62dca_hologram_uniform_monofractal_collapse_statement
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  xi_time_part62dca_hologram_uniform_monofractal_collapse_renyi_dimension_constancy D ∧
    xi_time_part62dca_hologram_uniform_monofractal_collapse_singleton_spectrum D

lemma xi_time_part62dca_hologram_uniform_monofractal_collapse_renyi_dimension_constancy_proof
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) :
    xi_time_part62dca_hologram_uniform_monofractal_collapse_renyi_dimension_constancy D := by
  intro _huniform B spectralBase tau Z hB hZ0 hZsucc htau
  exact paper_xi_time_part62dca_hologram_bernoulli_lq_spectrum
    B spectralBase tau Z hB hZ0 hZsucc htau

lemma xi_time_part62dca_hologram_uniform_monofractal_collapse_singleton_spectrum_proof
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) :
    xi_time_part62dca_hologram_uniform_monofractal_collapse_singleton_spectrum D := by
  intro huniform n w
  exact
    ⟨xi_time_part62dc_hologram_bernoulli_exact_dimensional_uniform_cylinder_mass
        D huniform n w,
      rfl⟩

/-- Paper label: `cor:xi-time-part62dca-hologram-uniform-monofractal-collapse`. -/
theorem paper_xi_time_part62dca_hologram_uniform_monofractal_collapse
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) :
    xi_time_part62dca_hologram_uniform_monofractal_collapse_statement D := by
  exact
    ⟨xi_time_part62dca_hologram_uniform_monofractal_collapse_renyi_dimension_constancy_proof D,
      xi_time_part62dca_hologram_uniform_monofractal_collapse_singleton_spectrum_proof D⟩

end Omega.Zeta
