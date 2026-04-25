import Omega.Zeta.XiTimePart63bFixedqSchurPacketExactInversion

namespace Omega.Zeta

/-- The cycle-type moment coordinates are the same class-function coordinates as the collision
coordinates appearing in the part63b exact inversion theorem. -/
def xi_time_part63c_frobenius_exact_inversion_cycle_moments_cycle_moment
    {q : ℕ} (cycle_coordinate : Fin q → ℚ) : Fin q → ℚ :=
  cycle_coordinate

/-- The singled-out single-cycle moment `C_(q)` is the corresponding coordinate evaluation. -/
def xi_time_part63c_frobenius_exact_inversion_cycle_moments_single_cycle
    {q : ℕ} (cycle_coordinate : Fin q → ℚ) (mu_q : Fin q) : ℚ :=
  xi_time_part63c_frobenius_exact_inversion_cycle_moments_cycle_moment cycle_coordinate mu_q

/-- Package the explicit part63b hypotheses into the previously proved fixed-`q` inversion
structure. -/
def xi_time_part63c_frobenius_exact_inversion_cycle_moments_packet
    (q : ℕ)
    (schur_character : Fin q → Fin q → ℚ)
    (schur_dimension cycle_weight schur_coordinate cycle_coordinate : Fin q → ℚ)
    (schur_dimension_ne_zero : ∀ lam, schur_dimension lam ≠ 0)
    (cycle_weight_ne_zero : ∀ mu, cycle_weight mu ≠ 0)
    (forward_tomography :
      ∀ lam,
        schur_coordinate lam / schur_dimension lam =
          ∑ mu,
            schur_character lam mu / cycle_weight mu *
              xi_time_part63c_frobenius_exact_inversion_cycle_moments_cycle_moment
                cycle_coordinate mu)
    (column_orthogonality :
      ∀ mu nu,
        ∑ lam, schur_character lam mu * schur_character lam nu =
          if mu = nu then cycle_weight mu else 0)
    (row_orthogonality :
      ∀ lam nu,
        ∑ mu, schur_character lam mu * schur_character nu mu / cycle_weight mu =
          if lam = nu then 1 else 0) :
    xi_time_part63b_fixedq_schur_packet_exact_inversion_data where
  q := q
  schur_character := schur_character
  schur_dimension := schur_dimension
  cycle_weight := cycle_weight
  schur_coordinate := schur_coordinate
  collision_coordinate :=
    xi_time_part63c_frobenius_exact_inversion_cycle_moments_cycle_moment cycle_coordinate
  schur_dimension_ne_zero := schur_dimension_ne_zero
  cycle_weight_ne_zero := cycle_weight_ne_zero
  forward_tomography := forward_tomography
  column_orthogonality := column_orthogonality
  row_orthogonality := row_orthogonality

/-- Paper label: `thm:xi-time-part63c-frobenius-exact-inversion-cycle-moments`.
This is the part63b exact inversion theorem rewritten in the cycle-moment coordinates `C_μ`,
with the singled-out coordinate `μ_q` recovering the single-cycle moment `S_q`. -/
theorem paper_xi_time_part63c_frobenius_exact_inversion_cycle_moments
    (q : ℕ)
    (schur_character : Fin q → Fin q → ℚ)
    (schur_dimension cycle_weight schur_coordinate cycle_coordinate : Fin q → ℚ)
    (schur_dimension_ne_zero : ∀ lam, schur_dimension lam ≠ 0)
    (cycle_weight_ne_zero : ∀ mu, cycle_weight mu ≠ 0)
    (forward_tomography :
      ∀ lam,
        schur_coordinate lam / schur_dimension lam =
          ∑ mu,
            schur_character lam mu / cycle_weight mu *
              xi_time_part63c_frobenius_exact_inversion_cycle_moments_cycle_moment
                cycle_coordinate mu)
    (column_orthogonality :
      ∀ mu nu,
        ∑ lam, schur_character lam mu * schur_character lam nu =
          if mu = nu then cycle_weight mu else 0)
    (row_orthogonality :
      ∀ lam nu,
        ∑ mu, schur_character lam mu * schur_character nu mu / cycle_weight mu =
          if lam = nu then 1 else 0)
    (mu_q : Fin q) :
    (∀ mu,
      xi_time_part63b_fixedq_schur_packet_exact_inversion_inverse_map
          (xi_time_part63c_frobenius_exact_inversion_cycle_moments_packet q schur_character
            schur_dimension cycle_weight schur_coordinate cycle_coordinate
            schur_dimension_ne_zero cycle_weight_ne_zero forward_tomography
            column_orthogonality row_orthogonality)
          schur_coordinate mu =
        xi_time_part63c_frobenius_exact_inversion_cycle_moments_cycle_moment
          cycle_coordinate mu) ∧
      xi_time_part63b_fixedq_schur_packet_exact_inversion_inverse_map
          (xi_time_part63c_frobenius_exact_inversion_cycle_moments_packet q schur_character
            schur_dimension cycle_weight schur_coordinate cycle_coordinate
            schur_dimension_ne_zero cycle_weight_ne_zero forward_tomography
            column_orthogonality row_orthogonality)
          schur_coordinate mu_q =
        xi_time_part63c_frobenius_exact_inversion_cycle_moments_single_cycle
          cycle_coordinate mu_q := by
  let D :=
    xi_time_part63c_frobenius_exact_inversion_cycle_moments_packet q schur_character
      schur_dimension cycle_weight schur_coordinate cycle_coordinate schur_dimension_ne_zero
      cycle_weight_ne_zero forward_tomography column_orthogonality row_orthogonality
  have hD := paper_xi_time_part63b_fixedq_schur_packet_exact_inversion D
  rcases hD with ⟨hcycle, _, _⟩
  refine ⟨?_, ?_⟩
  · intro mu
    simpa [D, xi_time_part63c_frobenius_exact_inversion_cycle_moments_cycle_moment] using
      hcycle mu
  · simpa [D, xi_time_part63c_frobenius_exact_inversion_cycle_moments_single_cycle,
      xi_time_part63c_frobenius_exact_inversion_cycle_moments_cycle_moment] using
      hcycle mu_q

end Omega.Zeta
