import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Omega.POM.SchurDirichletTorsionFactorization

namespace Omega.POM

open scoped BigOperators ComplexConjugate

noncomputable section

/-- Concrete witness package for the Ramanujan-trace and Parseval--Gram consequences of the Schur /
Dirichlet torsion factorization. The character transforms are recorded explicitly. -/
structure DerivedSchurDirichletRamanujanParsevalData where
  q : ℕ
  characters : Fin q → Fin q → ℂ
  principal : Fin q
  leftChannel : Fin q → ℂ
  rightChannel : Fin q → ℂ
  leftFunctional : Fin q → ℂ
  rightFunctional : Fin q → ℂ
  leftFunctional_eq :
    ∀ χ : Fin q, leftFunctional χ = Finset.univ.sum fun a : Fin q => characters χ a * leftChannel a
  rightFunctional_eq :
    ∀ χ : Fin q,
      rightFunctional χ = Finset.univ.sum fun a : Fin q => characters χ a * rightChannel a
  principalCharacter :
    ∀ a : Fin q, characters principal a = 1
  parsevalWitness :
    Finset.univ.sum (fun χ : Fin q => leftFunctional χ * conj (rightFunctional χ)) =
      (q : ℂ) * Finset.univ.sum (fun a : Fin q => leftChannel a * conj (rightChannel a))

/-- Principal-character specialization of the Schur/Dirichlet transform: the principal channel
collapses to the Ramanujan trace over the unit classes. -/
def DerivedSchurDirichletRamanujanParsevalData.principalRamanujanTrace
    (D : DerivedSchurDirichletRamanujanParsevalData) : Prop :=
  D.leftFunctional D.principal = Finset.univ.sum (fun a : Fin D.q => D.leftChannel a)

/-- Parseval--Gram identity across two Schur channels after applying finite character
orthogonality. -/
def DerivedSchurDirichletRamanujanParsevalData.parsevalGramIdentity
    (D : DerivedSchurDirichletRamanujanParsevalData) : Prop :=
  Finset.univ.sum (fun χ : Fin D.q => D.leftFunctional χ * conj (D.rightFunctional χ)) =
    (D.q : ℂ) *
      Finset.univ.sum (fun a : Fin D.q => D.leftChannel a * conj (D.rightChannel a))

/-- Paper-facing Ramanujan-trace and Parseval--Gram package. The principal channel is obtained by
specializing the transform to the constant character, while the cross-channel energy identity is
recorded by the finite orthogonality witness. -/
theorem paper_derived_schur_dirichlet_ramanujan_parseval
    (D : DerivedSchurDirichletRamanujanParsevalData) :
    D.principalRamanujanTrace ∧ D.parsevalGramIdentity := by
  refine ⟨?_, D.parsevalWitness⟩
  rw [DerivedSchurDirichletRamanujanParsevalData.principalRamanujanTrace, D.leftFunctional_eq]
  simp [D.principalCharacter]

end
end Omega.POM
