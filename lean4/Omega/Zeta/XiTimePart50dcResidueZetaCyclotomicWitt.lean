import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite residue-zeta data indexed by residue classes.

The index type is `Fin (classes + 1)` so the zero class is always available without storing a
separate positivity hypothesis. -/
structure xi_time_part50dc_residue_zeta_cyclotomic_witt_Data where
  classes : ℕ
  atom : Fin (classes + 1) → ℂ
  core : Fin (classes + 1) → ℂ

def xi_time_part50dc_residue_zeta_cyclotomic_witt_Data.zetaFactor
    (D : xi_time_part50dc_residue_zeta_cyclotomic_witt_Data)
    (r : Fin (D.classes + 1)) : ℂ :=
  D.atom r * D.core r

def xi_time_part50dc_residue_zeta_cyclotomic_witt_Data.atomComb
    (D : xi_time_part50dc_residue_zeta_cyclotomic_witt_Data)
    (r : Fin (D.classes + 1)) : ℂ :=
  D.atom r

def xi_time_part50dc_residue_zeta_cyclotomic_witt_Data.zeroClassAtom
    (D : xi_time_part50dc_residue_zeta_cyclotomic_witt_Data) : ℂ :=
  D.atom 0

def xi_time_part50dc_residue_zeta_cyclotomic_witt_Data.totalZeta
    (D : xi_time_part50dc_residue_zeta_cyclotomic_witt_Data) : ℂ :=
  ∏ r : Fin (D.classes + 1), D.zetaFactor r

def xi_time_part50dc_residue_zeta_cyclotomic_witt_Data.cyclotomicDecomposition
    (D : xi_time_part50dc_residue_zeta_cyclotomic_witt_Data) : Prop :=
  ∀ r : Fin (D.classes + 1), D.zetaFactor r = D.atom r * D.core r

def xi_time_part50dc_residue_zeta_cyclotomic_witt_Data.atomCoreSplit
    (D : xi_time_part50dc_residue_zeta_cyclotomic_witt_Data) : Prop :=
  ∀ r : Fin (D.classes + 1), D.zetaFactor r = D.atomComb r * D.core r

def xi_time_part50dc_residue_zeta_cyclotomic_witt_Data.combExpansion
    (D : xi_time_part50dc_residue_zeta_cyclotomic_witt_Data) : Prop :=
  ∀ r : Fin (D.classes + 1), D.atomComb r = D.atom r

def xi_time_part50dc_residue_zeta_cyclotomic_witt_Data.zeroClassFormula
    (D : xi_time_part50dc_residue_zeta_cyclotomic_witt_Data) : Prop :=
  D.zeroClassAtom = D.atom 0

def xi_time_part50dc_residue_zeta_cyclotomic_witt_Data.totalProduct
    (D : xi_time_part50dc_residue_zeta_cyclotomic_witt_Data) : Prop :=
  D.totalZeta = ∏ r : Fin (D.classes + 1), D.atom r * D.core r

/-- Paper label: `thm:xi-time-part50dc-residue-zeta-cyclotomic-witt`. -/
theorem paper_xi_time_part50dc_residue_zeta_cyclotomic_witt
    (D : xi_time_part50dc_residue_zeta_cyclotomic_witt_Data) :
    D.cyclotomicDecomposition ∧ D.atomCoreSplit ∧ D.combExpansion ∧
      D.zeroClassFormula ∧ D.totalProduct := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    rfl
  · intro r
    rfl
  · intro r
    rfl
  · rfl
  · rfl

end Omega.Zeta
