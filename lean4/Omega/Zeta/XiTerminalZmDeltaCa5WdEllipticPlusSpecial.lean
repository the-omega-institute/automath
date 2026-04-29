import Omega.Zeta.XiSemistableNodalFiberLocalEpsilonFactor

namespace Omega.Zeta

/-- Concrete certificate for the terminal `Z_m` delta `C_{A_5}` Weil--Deligne splitting. The
fields record the numerical invariants supplied by the nodal semistable and local-factor results. -/
structure xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_data where
  xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_prime : ℕ
  xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_ell : ℕ
  xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_monodromyRank : ℕ
  xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_ellipticDimension : ℕ
  xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_specialDimension : ℕ
  xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_conductorExponent : ℕ
  xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_nodeSign : ℤ
  xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_semistable_rank :
    xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_monodromyRank = 1
  xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_local_elliptic_dimension :
    xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_ellipticDimension = 2
  xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_local_special_dimension :
    xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_specialDimension = 2
  xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_local_conductor :
    xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_conductorExponent =
      xi_semistable_nodal_fiber_local_epsilon_factor_one_node_conductor

/-- Picard--Lefschetz monodromy has rank one at the single nodal semistable place. -/
def xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_data.monodromyRankOne
    (D : xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_data) : Prop :=
  D.xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_monodromyRank = 1

/-- The semisimple Weil part splits into a two-dimensional elliptic summand and a two-dimensional
special summand with the one-node conductor exponent. -/
def xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_data.semipsimpleSplitting
    (D : xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_data) : Prop :=
  D.xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_ellipticDimension = 2 ∧
    D.xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_specialDimension = 2 ∧
      D.xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_conductorExponent =
        xi_semistable_nodal_fiber_local_epsilon_factor_one_node_conductor

/-- The rank-one monodromy and two-dimensional special summand place the parameter in the
Siegel-parabolic local-Langlands class. -/
def xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_data.siegelParabolicType
    (D : xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_data) : Prop :=
  D.xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_monodromyRank = 1 ∧
    D.xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_specialDimension = 2

/-- Paper label: `prop:xi-terminal-zm-delta-ca5-wd-elliptic-plus-special`. -/
theorem paper_xi_terminal_zm_delta_ca5_wd_elliptic_plus_special
    (D : xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_data) :
    D.monodromyRankOne ∧ D.semipsimpleSplitting ∧ D.siegelParabolicType := by
  refine ⟨?_, ?_, ?_⟩
  · exact D.xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_semistable_rank
  · exact ⟨
      D.xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_local_elliptic_dimension,
      D.xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_local_special_dimension,
      D.xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_local_conductor⟩
  · exact ⟨
      D.xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_semistable_rank,
      D.xi_terminal_zm_delta_ca5_wd_elliptic_plus_special_local_special_dimension⟩

end Omega.Zeta
