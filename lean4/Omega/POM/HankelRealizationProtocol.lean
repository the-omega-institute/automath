import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic
import Omega.POM.HankelRankMinimal
import Omega.POM.StiffZeroHankelGoodReductionDimStability

namespace Omega.POM

/-- Concrete finite Hankel-shift package for the realization protocol. The integer matrix `A`
records the shift action `H₁ = H₀ A`; the adjugate identity then clears the determinant
denominator in the rational realization matrix. -/
structure pom_hankel_realization_protocol_data where
  pom_hankel_realization_protocol_d : ℕ
  pom_hankel_realization_protocol_sequence : ℕ → ℤ
  pom_hankel_realization_protocol_transition :
    Matrix (Fin pom_hankel_realization_protocol_d) (Fin pom_hankel_realization_protocol_d) ℤ
  pom_hankel_realization_protocol_shift :
    hankelBlock pom_hankel_realization_protocol_d 1 pom_hankel_realization_protocol_sequence =
      hankelBlock pom_hankel_realization_protocol_d 0 pom_hankel_realization_protocol_sequence *
        pom_hankel_realization_protocol_transition

namespace pom_hankel_realization_protocol_data

/-- The same integer sequence, viewed over `ℚ`, for the rank/minimal-realization certificate. -/
def pom_hankel_realization_protocol_rat_sequence
    (D : pom_hankel_realization_protocol_data) : ℕ → ℚ :=
  fun n => D.pom_hankel_realization_protocol_sequence n

/-- The determinant-cleared inverse formula is the denominator-control component of the Hankel
realization protocol. -/
def denominators_dvd_hankel_det (D : pom_hankel_realization_protocol_data) : Prop :=
  hankelTransitionDenominatorCleared D.pom_hankel_realization_protocol_sequence
    D.pom_hankel_realization_protocol_transition

/-- The minimal-realization certificate combines the Hankel-rank/minimal-dimension equality with
the determinant-cleared construction of the shift matrix. -/
def has_minimal_realization (D : pom_hankel_realization_protocol_data) : Prop :=
  hankel_rank_minimal_hankelRank D.pom_hankel_realization_protocol_rat_sequence =
      sInf {r : ℕ |
        hankel_rank_minimal_hasLinearRepresentation
          D.pom_hankel_realization_protocol_rat_sequence r} ∧
    D.denominators_dvd_hankel_det

end pom_hankel_realization_protocol_data

/-- The shift identity `H₁ = H₀ A` gives the determinant-controlled adjugate formula
`det(H₀) A = adj(H₀) H₁`. -/
theorem pom_hankel_realization_protocol_denominator_cleared
    (D : pom_hankel_realization_protocol_data) :
    D.denominators_dvd_hankel_det := by
  let H0 : Matrix (Fin D.pom_hankel_realization_protocol_d)
      (Fin D.pom_hankel_realization_protocol_d) ℤ :=
    hankelBlock D.pom_hankel_realization_protocol_d 0
      D.pom_hankel_realization_protocol_sequence
  let H1 : Matrix (Fin D.pom_hankel_realization_protocol_d)
      (Fin D.pom_hankel_realization_protocol_d) ℤ :=
    hankelBlock D.pom_hankel_realization_protocol_d 1
      D.pom_hankel_realization_protocol_sequence
  have hshift' : H1 = H0 * D.pom_hankel_realization_protocol_transition := by
    simpa [H0, H1] using D.pom_hankel_realization_protocol_shift
  have hclear :
      H0.det • D.pom_hankel_realization_protocol_transition = H0.adjugate * H1 := by
    calc
      H0.det • D.pom_hankel_realization_protocol_transition =
          (H0.det • (1 : Matrix (Fin D.pom_hankel_realization_protocol_d)
            (Fin D.pom_hankel_realization_protocol_d) ℤ)) *
            D.pom_hankel_realization_protocol_transition := by simp
      _ = (H0.adjugate * H0) * D.pom_hankel_realization_protocol_transition := by
        rw [Matrix.adjugate_mul]
      _ = H0.adjugate * (H0 * D.pom_hankel_realization_protocol_transition) := by
        rw [Matrix.mul_assoc]
      _ = H0.adjugate * H1 := by rw [hshift']
  simpa [pom_hankel_realization_protocol_data.denominators_dvd_hankel_det,
    hankelTransitionDenominatorCleared, H0, H1] using hclear

/-- Paper label: `prop:pom-hankel-realization-protocol`. -/
theorem paper_pom_hankel_realization_protocol
    (D : pom_hankel_realization_protocol_data) :
    D.has_minimal_realization ∧ D.denominators_dvd_hankel_det := by
  have hdet := pom_hankel_realization_protocol_denominator_cleared D
  refine ⟨?_, hdet⟩
  exact ⟨paper_hankel_rank_minimal D.pom_hankel_realization_protocol_rat_sequence, hdet⟩

end Omega.POM
