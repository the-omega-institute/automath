import Omega.Zeta.XiTimePart63bFixedqSchurPacketExactInversion

namespace Omega.Zeta

/-- Paper label:
`cor:xi-time-part63b-fixedq-schur-packet-recovers-low-moments-primitives`. -/
theorem paper_xi_time_part63b_fixedq_schur_packet_recovers_low_moments_primitives
    (D : xi_time_part63b_fixedq_schur_packet_exact_inversion_data) :
    ∀ r : Fin D.q,
      xi_time_part63b_fixedq_schur_packet_exact_inversion_inverse_map D D.schur_coordinate r =
        D.collision_coordinate r := by
  exact (paper_xi_time_part63b_fixedq_schur_packet_exact_inversion D).1

end Omega.Zeta
