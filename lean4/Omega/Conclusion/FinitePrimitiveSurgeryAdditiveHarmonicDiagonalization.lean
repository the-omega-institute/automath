import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite primitive-surgery data.  Each atom has an integer weight, a length, and the
finite harmonic character used to diagonalize the additive residue projections. -/
structure conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_data where
  conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_atomCount : Nat
  conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_residueModulus : Nat
  conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_modulus_pos :
    0 <
      conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_residueModulus
  conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_atomWeight :
    Fin conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_atomCount → Int
  conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_atomLength :
    Fin conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_atomCount → Nat
  conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_character : Nat → Int

/-- Residue of an atom length modulo the surgery modulus. -/
def conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_lengthResidue
    (D : conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_data)
    (a : Fin
      D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_atomCount) :
    Nat :=
  D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_atomLength a %
    D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_residueModulus

/-- Projection of the finite atom sum onto one length-residue class. -/
def conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_residueProjection
    (D : conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_data)
    (r : Nat) : Int :=
  Finset.sum Finset.univ fun a : Fin
    D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_atomCount =>
      if conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_lengthResidue D a =
          r %
            D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_residueModulus then
        D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_atomWeight a
      else
        0

/-- Sum of all harmonic channels after residue projection. -/
def conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_harmonicSide
    (D : conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_data) : Int :=
  Finset.sum
    (Finset.range
      D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_residueModulus)
    (fun r =>
      D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_character r *
        conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_residueProjection D r)

/-- Direct atom-side finite harmonic transform. -/
def conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_atomSide
    (D : conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_data) : Int :=
  Finset.sum Finset.univ fun a : Fin
    D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_atomCount =>
      D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_character
          (conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_lengthResidue D a) *
        D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_atomWeight a

namespace conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_data

/-- The residue projection formula is the finite atom sum filtered by length residue. -/
def residueProjectionFormula
    (D : conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_data) : Prop :=
  ∀ r : Nat,
    conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_residueProjection D r =
      Finset.sum
        ((Finset.univ : Finset
          (Fin
            D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_atomCount)
        ).filter
          (fun a =>
            conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_lengthResidue
                D a =
              r %
                D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_residueModulus))
        (fun a =>
          D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_atomWeight a)

/-- The additive character channel diagonalizes the finite residue projections. -/
def characterFormula
    (D : conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_data) : Prop :=
  conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_harmonicSide D =
    conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_atomSide D

end conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_data

/-- Paper label:
`thm:conclusion-finite-primitive-surgery-additive-harmonic-diagonalization`. -/
theorem paper_conclusion_finite_primitive_surgery_additive_harmonic_diagonalization
    (D : conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_data) :
    D.residueProjectionFormula ∧ D.characterFormula := by
  constructor
  · intro r
    rw [conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_residueProjection]
    rw [Finset.sum_filter]
  · simp only [conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_data.characterFormula,
      conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_harmonicSide,
      conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_residueProjection,
      conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_atomSide]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro a ha
    have hmem :
        conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_lengthResidue D a ∈
          Finset.range
            D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_residueModulus :=
      Finset.mem_range.mpr
        (Nat.mod_lt _
          D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_modulus_pos)
    rw [Finset.sum_eq_single
      (conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_lengthResidue D a)]
    · have hres_lt :
          conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_lengthResidue D a <
            D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_residueModulus :=
        Finset.mem_range.mp hmem
      simp [Nat.mod_eq_of_lt hres_lt]
    · intro b hb hne
      have hbne :
          conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_lengthResidue D a ≠
            b %
              D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_residueModulus := by
        have hb_lt :
            b <
              D.conclusion_finite_primitive_surgery_additive_harmonic_diagonalization_residueModulus :=
          Finset.mem_range.mp hb
        simpa [Nat.mod_eq_of_lt hb_lt] using hne.symm
      simp [hbne]
    · intro hnot
      exact (hnot hmem).elim

end Omega.Conclusion
