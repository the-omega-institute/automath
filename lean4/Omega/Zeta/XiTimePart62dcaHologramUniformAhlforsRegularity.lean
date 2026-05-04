import Omega.Zeta.XiTimePart62dcaHologramAffineIFSFixedpointEquation

namespace Omega.Zeta

open scoped BigOperators

/-- Uniform cylinder masses for the label
`cor:xi-time-part62dca-hologram-uniform-ahlfors-regularity`. -/
noncomputable def xi_time_part62dca_hologram_uniform_ahlfors_regularity_uniform_cylinder_mass
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  (∀ i,
      D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_probability i =
        (D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card : ℝ)⁻¹) →
    ∀ n (w : D.addr_prefix n),
      D.cylinder_mass w =
        ((D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card : ℝ)⁻¹) ^ n

/-- Cylinder-ball identification for the label
`cor:xi-time-part62dca-hologram-uniform-ahlfors-regularity`. -/
noncomputable def xi_time_part62dca_hologram_uniform_ahlfors_regularity_cylinder_ball_identification
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  ∀ n (w : D.addr_prefix n), D.ball_mass w = D.cylinder_mass w

/-- Uniform ball mass law for the label
`cor:xi-time-part62dca-hologram-uniform-ahlfors-regularity`. -/
noncomputable def xi_time_part62dca_hologram_uniform_ahlfors_regularity_uniform_ball_mass
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  (∀ i,
      D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_probability i =
        (D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card : ℝ)⁻¹) →
    ∀ n (w : D.addr_prefix n),
      D.ball_mass w =
        ((D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card : ℝ)⁻¹) ^ n

/-- A finite-depth Ahlfors-regularity package for uniform hologram balls. -/
noncomputable def xi_time_part62dca_hologram_uniform_ahlfors_regularity_ahlfors_regular
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  (∀ i,
      D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_probability i =
        (D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card : ℝ)⁻¹) →
    ∀ n (w : D.addr_prefix n),
      D.ball_mass w =
          ((D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card : ℝ)⁻¹) ^ n ∧
        D.ball_mass w = D.cylinder_mass w

/-- The depth-zero hologram content is finite and positive. -/
noncomputable def xi_time_part62dca_hologram_uniform_ahlfors_regularity_finite_positive_hausdorff_content
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  ∃ w : D.addr_prefix 0, 0 < D.ball_mass w ∧ D.ball_mass w = 1

/-- Statement package for
`cor:xi-time-part62dca-hologram-uniform-ahlfors-regularity`. -/
noncomputable def xi_time_part62dca_hologram_uniform_ahlfors_regularity_statement
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  xi_time_part62dca_hologram_uniform_ahlfors_regularity_uniform_cylinder_mass D ∧
    xi_time_part62dca_hologram_uniform_ahlfors_regularity_cylinder_ball_identification D ∧
      xi_time_part62dca_hologram_uniform_ahlfors_regularity_uniform_ball_mass D ∧
        xi_time_part62dca_hologram_uniform_ahlfors_regularity_ahlfors_regular D ∧
          xi_time_part62dca_hologram_uniform_ahlfors_regularity_finite_positive_hausdorff_content D

lemma xi_time_part62dca_hologram_uniform_ahlfors_regularity_uniform_cylinder_mass_proof
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) :
    xi_time_part62dca_hologram_uniform_ahlfors_regularity_uniform_cylinder_mass D := by
  intro huniform n w
  simpa [xi_time_part62dc_hologram_bernoulli_exact_dimensional_data.ball_mass] using
    xi_time_part62dc_hologram_bernoulli_exact_dimensional_uniform_cylinder_mass D huniform n w

lemma xi_time_part62dca_hologram_uniform_ahlfors_regularity_cylinder_ball_identification_proof
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) :
    xi_time_part62dca_hologram_uniform_ahlfors_regularity_cylinder_ball_identification D := by
  exact (paper_xi_time_part62dca_hologram_affine_ifs_fixedpoint_equation D).1

lemma xi_time_part62dca_hologram_uniform_ahlfors_regularity_uniform_ball_mass_proof
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) :
    xi_time_part62dca_hologram_uniform_ahlfors_regularity_uniform_ball_mass D := by
  exact (paper_xi_time_part62dc_hologram_bernoulli_exact_dimensional D).2.2.1

lemma xi_time_part62dca_hologram_uniform_ahlfors_regularity_ahlfors_regular_proof
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) :
    xi_time_part62dca_hologram_uniform_ahlfors_regularity_ahlfors_regular D := by
  intro huniform n w
  exact
    ⟨xi_time_part62dca_hologram_uniform_ahlfors_regularity_uniform_ball_mass_proof
        D huniform n w,
      xi_time_part62dca_hologram_uniform_ahlfors_regularity_cylinder_ball_identification_proof
        D n w⟩

lemma xi_time_part62dca_hologram_uniform_ahlfors_regularity_finite_positive_hausdorff_content_proof
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) :
    xi_time_part62dca_hologram_uniform_ahlfors_regularity_finite_positive_hausdorff_content D := by
  refine ⟨(fun i => Fin.elim0 i), ?_, ?_⟩
  · simp [xi_time_part62dc_hologram_bernoulli_exact_dimensional_data.ball_mass,
      xi_time_part62dc_hologram_bernoulli_exact_dimensional_data.cylinder_mass]
  · simp [xi_time_part62dc_hologram_bernoulli_exact_dimensional_data.ball_mass,
      xi_time_part62dc_hologram_bernoulli_exact_dimensional_data.cylinder_mass]

/-- Paper label: `cor:xi-time-part62dca-hologram-uniform-ahlfors-regularity`. -/
theorem paper_xi_time_part62dca_hologram_uniform_ahlfors_regularity
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) :
    xi_time_part62dca_hologram_uniform_ahlfors_regularity_statement D := by
  exact
    ⟨xi_time_part62dca_hologram_uniform_ahlfors_regularity_uniform_cylinder_mass_proof D,
      xi_time_part62dca_hologram_uniform_ahlfors_regularity_cylinder_ball_identification_proof D,
      xi_time_part62dca_hologram_uniform_ahlfors_regularity_uniform_ball_mass_proof D,
      xi_time_part62dca_hologram_uniform_ahlfors_regularity_ahlfors_regular_proof D,
      xi_time_part62dca_hologram_uniform_ahlfors_regularity_finite_positive_hausdorff_content_proof D⟩

end Omega.Zeta
