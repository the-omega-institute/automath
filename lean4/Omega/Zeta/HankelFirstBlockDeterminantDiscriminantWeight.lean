import Mathlib.Tactic
import Omega.Zeta.HankelDeterminantalRadicalEqRigidity

namespace Omega.Zeta

/-- Chapter-local corollary package for the first Hankel block determinant factorization. The
prime-obstruction clause is extracted from the one-step rank-drop witness together with the
radical-rigidity theorem. -/
structure HankelFirstBlockDeterminantDiscriminantWeightData where
  weight1 : ℤ
  weight2 : ℤ
  weight3 : ℤ
  atom1 : ℤ
  atom2 : ℤ
  atom3 : ℤ
  firstBlockDeterminantFactorization : Prop
  factorization_iff :
    firstBlockDeterminantFactorization ↔
      (hankel3 weight1 weight2 weight3 atom1 atom2 atom3).det =
        weight1 * weight2 * weight3 * (atom2 - atom1)^2 * (atom3 - atom1)^2 *
          (atom3 - atom2)^2
  rankDropPrimeObstruction : Prop
  rankDropWitness : (hankel3 weight1 weight2 weight3 atom1 atom2 atom3).det = 0
  obstruction_of_radical :
    (weight1 = 0 ∨ weight2 = 0 ∨ weight3 = 0 ∨ atom1 = atom2 ∨ atom1 = atom3 ∨
      atom2 = atom3) → rankDropPrimeObstruction

/-- The first Hankel principal block factors as weight product times squared discriminant, and a
rank drop forces the corresponding weight/discriminant obstruction.
    cor:xi-hankel-first-block-determinant-discriminant-weight -/
theorem paper_xi_hankel_first_block_determinant_discriminant_weight
    (D : HankelFirstBlockDeterminantDiscriminantWeightData) :
    D.firstBlockDeterminantFactorization ∧ D.rankDropPrimeObstruction := by
  have hpack := paper_xi_hankel_determinantal_radical_eq_rigidity
  have hfactor :
      (hankel3 D.weight1 D.weight2 D.weight3 D.atom1 D.atom2 D.atom3).det =
        D.weight1 * D.weight2 * D.weight3 * (D.atom2 - D.atom1)^2 * (D.atom3 - D.atom1)^2 *
          (D.atom3 - D.atom2)^2 :=
    hpack.1 D.weight1 D.weight2 D.weight3 D.atom1 D.atom2 D.atom3
  have hradical :
      D.weight1 = 0 ∨ D.weight2 = 0 ∨ D.weight3 = 0 ∨ D.atom1 = D.atom2 ∨
        D.atom1 = D.atom3 ∨ D.atom2 = D.atom3 :=
    (hpack.2 D.weight1 D.weight2 D.weight3 D.atom1 D.atom2 D.atom3).1 D.rankDropWitness
  exact ⟨D.factorization_iff.mpr hfactor, D.obstruction_of_radical hradical⟩

end Omega.Zeta
