import Mathlib.Data.Nat.Basic

namespace Omega.Zeta

universe u v w

/-- Concrete endomorphism-algebra maps for the `V_2` Jacobian block.

The dimension identity records the paper's `A_V2 = J(Z)^2` bookkeeping, while the two injectivity
hypotheses encode the cyclotomic norm-square inclusion and the block-diagonal Jacobian projector
inclusion. -/
structure xi_time_part9n1a_v2_block_eisenstein_multiplication_data where
  xi_time_part9n1a_v2_block_eisenstein_multiplication_EisensteinField : Type u
  xi_time_part9n1a_v2_block_eisenstein_multiplication_AV2End : Type v
  xi_time_part9n1a_v2_block_eisenstein_multiplication_JXEnd : Type w
  xi_time_part9n1a_v2_block_eisenstein_multiplication_av2Dimension : ℕ
  xi_time_part9n1a_v2_block_eisenstein_multiplication_jzDimension : ℕ
  xi_time_part9n1a_v2_block_eisenstein_multiplication_av2_eq_jz_square :
    xi_time_part9n1a_v2_block_eisenstein_multiplication_av2Dimension =
      xi_time_part9n1a_v2_block_eisenstein_multiplication_jzDimension *
        xi_time_part9n1a_v2_block_eisenstein_multiplication_jzDimension
  xi_time_part9n1a_v2_block_eisenstein_multiplication_cyclotomicNormSquare :
    xi_time_part9n1a_v2_block_eisenstein_multiplication_EisensteinField →
      xi_time_part9n1a_v2_block_eisenstein_multiplication_AV2End
  xi_time_part9n1a_v2_block_eisenstein_multiplication_blockDiagonalProjector :
    xi_time_part9n1a_v2_block_eisenstein_multiplication_AV2End →
      xi_time_part9n1a_v2_block_eisenstein_multiplication_JXEnd
  xi_time_part9n1a_v2_block_eisenstein_multiplication_cyclotomicNormSquare_injective :
    Function.Injective
      xi_time_part9n1a_v2_block_eisenstein_multiplication_cyclotomicNormSquare
  xi_time_part9n1a_v2_block_eisenstein_multiplication_blockDiagonalProjector_injective :
    Function.Injective
      xi_time_part9n1a_v2_block_eisenstein_multiplication_blockDiagonalProjector

namespace xi_time_part9n1a_v2_block_eisenstein_multiplication_data

/-- The Eisenstein field embeds into the `V_2` endomorphism algebra. -/
def eisensteinFieldEmbedsAV2
    (D : xi_time_part9n1a_v2_block_eisenstein_multiplication_data) : Prop :=
  Function.Injective
    D.xi_time_part9n1a_v2_block_eisenstein_multiplication_cyclotomicNormSquare

/-- The `V_2` endomorphism algebra embeds into the full Jacobian endomorphism algebra, and hence
the composed Eisenstein action remains faithful after transport. -/
def av2EndEmbedsJX
    (D : xi_time_part9n1a_v2_block_eisenstein_multiplication_data) : Prop :=
  Function.Injective
      D.xi_time_part9n1a_v2_block_eisenstein_multiplication_blockDiagonalProjector ∧
    Function.Injective
      (fun x =>
        D.xi_time_part9n1a_v2_block_eisenstein_multiplication_blockDiagonalProjector
          (D.xi_time_part9n1a_v2_block_eisenstein_multiplication_cyclotomicNormSquare x))

end xi_time_part9n1a_v2_block_eisenstein_multiplication_data

/-- Paper label: `cor:xi-time-part9n1a-v2-block-eisenstein-multiplication`. -/
theorem paper_xi_time_part9n1a_v2_block_eisenstein_multiplication
    (D : xi_time_part9n1a_v2_block_eisenstein_multiplication_data) :
    D.eisensteinFieldEmbedsAV2 ∧ D.av2EndEmbedsJX := by
  constructor
  · exact D.xi_time_part9n1a_v2_block_eisenstein_multiplication_cyclotomicNormSquare_injective
  · constructor
    · exact D.xi_time_part9n1a_v2_block_eisenstein_multiplication_blockDiagonalProjector_injective
    · intro x y hxy
      apply D.xi_time_part9n1a_v2_block_eisenstein_multiplication_cyclotomicNormSquare_injective
      exact
        D.xi_time_part9n1a_v2_block_eisenstein_multiplication_blockDiagonalProjector_injective hxy

end Omega.Zeta
