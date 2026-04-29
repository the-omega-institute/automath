import Omega.Zeta.XiTimePart62dcaHologramUniformAhlforsRegularity

namespace Omega.Zeta

/-- Total Hausdorff mass one in the finite-prefix hologram interface. -/
noncomputable def xi_time_part62dca_hologram_hausdorff_measure_identification_total_mass_one
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  ∃ w : D.addr_prefix 0, D.ball_mass w = 1

/-- Restricted Hausdorff mass agrees with the Bernoulli cylinder mass on every prefix. -/
noncomputable def xi_time_part62dca_hologram_hausdorff_measure_identification_restricted_measure_eq
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  ∀ n (w : D.addr_prefix n), D.ball_mass w = D.cylinder_mass w

/-- After normalizing by the total mass one, the restricted hologram mass is unchanged. -/
noncomputable def xi_time_part62dca_hologram_hausdorff_measure_identification_normalized_restriction_eq
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  ∀ n (w : D.addr_prefix n), D.ball_mass w / 1 = D.cylinder_mass w

/-- Statement package for
`cor:xi-time-part62dca-hologram-hausdorff-measure-identification`. -/
noncomputable def xi_time_part62dca_hologram_hausdorff_measure_identification_statement
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  xi_time_part62dca_hologram_hausdorff_measure_identification_total_mass_one D ∧
    xi_time_part62dca_hologram_hausdorff_measure_identification_restricted_measure_eq D ∧
      xi_time_part62dca_hologram_hausdorff_measure_identification_normalized_restriction_eq D

lemma xi_time_part62dca_hologram_hausdorff_measure_identification_total_mass_one_proof
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) :
    xi_time_part62dca_hologram_hausdorff_measure_identification_total_mass_one D := by
  rcases
    (paper_xi_time_part62dca_hologram_uniform_ahlfors_regularity D).2.2.2.2 with
    ⟨w, _hw_pos, hw_one⟩
  exact ⟨w, hw_one⟩

lemma xi_time_part62dca_hologram_hausdorff_measure_identification_restricted_measure_eq_proof
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) :
    xi_time_part62dca_hologram_hausdorff_measure_identification_restricted_measure_eq D := by
  exact (paper_xi_time_part62dca_hologram_uniform_ahlfors_regularity D).2.1

lemma xi_time_part62dca_hologram_hausdorff_measure_identification_normalized_restriction_eq_proof
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) :
    xi_time_part62dca_hologram_hausdorff_measure_identification_normalized_restriction_eq D := by
  intro n w
  simpa using
    xi_time_part62dca_hologram_hausdorff_measure_identification_restricted_measure_eq_proof
      D n w

/-- Paper label: `cor:xi-time-part62dca-hologram-hausdorff-measure-identification`. -/
theorem paper_xi_time_part62dca_hologram_hausdorff_measure_identification
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) :
    xi_time_part62dca_hologram_hausdorff_measure_identification_statement D := by
  exact
    ⟨xi_time_part62dca_hologram_hausdorff_measure_identification_total_mass_one_proof D,
      xi_time_part62dca_hologram_hausdorff_measure_identification_restricted_measure_eq_proof D,
      xi_time_part62dca_hologram_hausdorff_measure_identification_normalized_restriction_eq_proof
        D⟩

end Omega.Zeta
