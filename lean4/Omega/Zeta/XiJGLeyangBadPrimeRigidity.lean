import Omega.Zeta.XiJGDiscriminantSquareclassInvariance

namespace Omega.Zeta

/-- A discriminant is square in the ambient field. -/
def xi_jg_leyang_bad_prime_rigidity_is_square {K : Type*} [Field K] (disc : K) : Prop :=
  ∃ u : K, disc = u ^ 2

/-- The quadratic-resolution layer detected by the discriminant squareclass. -/
def xi_jg_leyang_bad_prime_rigidity_quadratic_resolution_layer {K : Type*} [Field K]
    (disc : K) : Prop :=
  xi_jg_leyang_bad_prime_rigidity_is_square disc

lemma xi_jg_leyang_bad_prime_rigidity_square_mul_square_iff {K : Type*} [Field K]
    (disc u : K) (hu : u ≠ 0) :
    xi_jg_leyang_bad_prime_rigidity_is_square disc ↔
      xi_jg_leyang_bad_prime_rigidity_is_square (disc * u ^ 2) := by
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨v * u, ?_⟩
    ring
  · rintro ⟨v, hv⟩
    refine ⟨v / u, ?_⟩
    have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
    apply mul_right_cancel₀ hu2
    rw [hv]
    field_simp [hu]

/-- Paper label: `cor:xi-jg-leyang-bad-prime-rigidity`.

The transported discriminant differs from the original one by a nonzero square factor, so
square-discriminant criteria and the induced quadratic-resolution layer are preserved. -/
theorem paper_xi_jg_leyang_bad_prime_rigidity {K : Type*} [Field K]
    (D : Omega.GU.JoukowskyGodelTransportData K) (discP B : K)
    (ha0 : D.a_0 ≠ 0) (hB : B ≠ 0) :
    (xi_jg_leyang_bad_prime_rigidity_is_square discP ↔
        xi_jg_leyang_bad_prime_rigidity_is_square
          (xi_jg_discriminant_squareclass_invariance_transport_discriminant D discP B)) ∧
      xi_jg_leyang_bad_prime_rigidity_quadratic_resolution_layer discP =
        xi_jg_leyang_bad_prime_rigidity_quadratic_resolution_layer
          (xi_jg_discriminant_squareclass_invariance_transport_discriminant D discP B) := by
  let squareFactor := xi_jg_discriminant_squareclass_invariance_square_factor D B
  have hsquareFactor : squareFactor ≠ 0 := by
    dsimp [squareFactor, xi_jg_discriminant_squareclass_invariance_square_factor]
    exact mul_ne_zero (pow_ne_zero _ ha0) hB
  have htransport :
      xi_jg_discriminant_squareclass_invariance_transport_discriminant D discP B =
        discP * squareFactor ^ 2 := by
    simpa [squareFactor] using
      xi_jg_discriminant_squareclass_invariance_transport_rewrite D discP B
  have hsquare :
      xi_jg_leyang_bad_prime_rigidity_is_square discP ↔
        xi_jg_leyang_bad_prime_rigidity_is_square
          (xi_jg_discriminant_squareclass_invariance_transport_discriminant D discP B) := by
    rw [htransport]
    exact xi_jg_leyang_bad_prime_rigidity_square_mul_square_iff discP squareFactor hsquareFactor
  exact ⟨hsquare, propext hsquare⟩

end Omega.Zeta
