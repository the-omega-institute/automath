import Mathlib.Tactic
import Omega.GU.JoukowskyGodelLeadingCoeffRigidity

namespace Omega.Zeta

open Omega.GU

/-- The square factor produced by the transported root-difference product. -/
def xi_jg_discriminant_squareclass_invariance_square_factor {K : Type*} [Field K]
    (D : JoukowskyGodelTransportData K) (B : K) : K :=
  D.a_0 ^ (D.n - 1) * B

/-- The transported discriminant model differs from the original one by an explicit square factor
coming from the constant term and the symmetric root expression. -/
def xi_jg_discriminant_squareclass_invariance_transport_discriminant {K : Type*} [Field K]
    (D : JoukowskyGodelTransportData K) (discP B : K) : K :=
  D.a_0 ^ (2 * (D.n - 1)) * discP * B ^ 2

lemma xi_jg_discriminant_squareclass_invariance_transport_rewrite {K : Type*} [Field K]
    (D : JoukowskyGodelTransportData K) (discP B : K) :
    xi_jg_discriminant_squareclass_invariance_transport_discriminant D discP B =
      discP * xi_jg_discriminant_squareclass_invariance_square_factor D B ^ 2 := by
  dsimp [xi_jg_discriminant_squareclass_invariance_transport_discriminant,
    xi_jg_discriminant_squareclass_invariance_square_factor]
  calc
    D.a_0 ^ (2 * (D.n - 1)) * discP * B ^ 2
        = discP * (D.a_0 ^ (2 * (D.n - 1)) * B ^ 2) := by ring
    _ = discP * ((D.a_0 ^ (D.n - 1)) ^ 2 * B ^ 2) := by
      rw [Nat.mul_comm, pow_mul]
    _ = discP * (D.a_0 ^ (D.n - 1) * B) ^ 2 := by ring

/-- Paper label: `thm:xi-jg-discriminant-squareclass-invariance`. In the transported
Joukowsky--Godel discriminant model, the quotient by the original discriminant is an explicit
square, hence the squareclass is unchanged. -/
theorem paper_xi_jg_discriminant_squareclass_invariance {K : Type*} [Field K]
    (D : JoukowskyGodelTransportData K) (discP B : K) :
    ∃ u : K,
      xi_jg_discriminant_squareclass_invariance_transport_discriminant D discP B =
        discP * u ^ 2 := by
  refine ⟨xi_jg_discriminant_squareclass_invariance_square_factor D B, ?_⟩
  exact xi_jg_discriminant_squareclass_invariance_transport_rewrite D discP B

end Omega.Zeta
