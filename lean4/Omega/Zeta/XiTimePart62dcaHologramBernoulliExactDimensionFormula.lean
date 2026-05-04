import Omega.Zeta.XiTimePart62dcaHologramAffineIFSFixedpointEquation

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-time-part62dca-hologram-bernoulli-exact-dimension-formula`.
The affine IFS fixed-point wrapper supplies exact dimensionality and the Bernoulli cylinder
product formula; the entropy/log-base local and Hausdorff dimension identities are definitional
in the existing Bernoulli data interface. -/
theorem paper_xi_time_part62dca_hologram_bernoulli_exact_dimension_formula
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) :
    D.exact_dimensional ∧
      (∀ n (w : D.addr_prefix n), D.ball_mass w =
        ∏ i : Fin n,
          D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_probability (w i)) ∧
      D.local_dimension_formula ∧ D.hausdorff_dimension_formula := by
  have hIFS := paper_xi_time_part62dca_hologram_affine_ifs_fixedpoint_equation D
  exact ⟨hIFS.1, hIFS.2, rfl, rfl⟩

end Omega.Zeta
