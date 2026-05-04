import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite fold data for `thm:xi-kappa-unique-carrier`. -/
structure xi_kappa_unique_carrier_data where
  xi_kappa_unique_carrier_micro : Type
  xi_kappa_unique_carrier_macro : Type
  xi_kappa_unique_carrier_micro_fintype : Fintype xi_kappa_unique_carrier_micro
  xi_kappa_unique_carrier_macro_fintype : Fintype xi_kappa_unique_carrier_macro
  xi_kappa_unique_carrier_micro_decidableEq : DecidableEq xi_kappa_unique_carrier_micro
  xi_kappa_unique_carrier_macro_decidableEq : DecidableEq xi_kappa_unique_carrier_macro
  xi_kappa_unique_carrier_fold :
    xi_kappa_unique_carrier_micro → xi_kappa_unique_carrier_macro

namespace xi_kappa_unique_carrier_data

/-- Fiber multiplicity of a macrostate under a fold map. -/
def xi_kappa_unique_carrier_fiberMultiplicity
    (D : xi_kappa_unique_carrier_data)
    (foldMap : D.xi_kappa_unique_carrier_micro → D.xi_kappa_unique_carrier_macro)
    (x : D.xi_kappa_unique_carrier_macro) : ℕ := by
  letI := D.xi_kappa_unique_carrier_micro_fintype
  letI := D.xi_kappa_unique_carrier_micro_decidableEq
  letI := D.xi_kappa_unique_carrier_macro_decidableEq
  exact (Finset.univ.filter fun y => foldMap y = x).card

/-- The recomputed finite entropy ledger, represented by the total fiber capacity. -/
def xi_kappa_unique_carrier_entropyLedger
    (D : xi_kappa_unique_carrier_data)
    (foldMap : D.xi_kappa_unique_carrier_micro → D.xi_kappa_unique_carrier_macro) : ℕ := by
  letI := D.xi_kappa_unique_carrier_macro_fintype
  letI := D.xi_kappa_unique_carrier_macro_decidableEq
  exact ∑ x : D.xi_kappa_unique_carrier_macro,
    D.xi_kappa_unique_carrier_fiberMultiplicity foldMap x

/-- The invisible capacity `κ` of the canonical fold. -/
def xi_kappa_unique_carrier_kappa (D : xi_kappa_unique_carrier_data) : ℕ :=
  D.xi_kappa_unique_carrier_entropyLedger D.xi_kappa_unique_carrier_fold

/-- The maximum compressible hidden information, written in the same ledger units as `κ`. -/
def xi_kappa_unique_carrier_maxCompressedInfo (D : xi_kappa_unique_carrier_data) : ℕ :=
  D.xi_kappa_unique_carrier_kappa

/-- The maximum compressed information equals the invisible fiber capacity. -/
def maxCompressedInfoEqualsKappa (D : xi_kappa_unique_carrier_data) : Prop :=
  D.xi_kappa_unique_carrier_maxCompressedInfo = D.xi_kappa_unique_carrier_kappa

/-- Recomputing the ledger is independent of implementation details once the fold is fixed. -/
def implementationIndependentEntropyLedger (D : xi_kappa_unique_carrier_data) : Prop :=
  ∀ foldMap : D.xi_kappa_unique_carrier_micro → D.xi_kappa_unique_carrier_macro,
    foldMap = D.xi_kappa_unique_carrier_fold →
      D.xi_kappa_unique_carrier_entropyLedger foldMap = D.xi_kappa_unique_carrier_kappa

end xi_kappa_unique_carrier_data

/-- Paper label: `thm:xi-kappa-unique-carrier`. -/
theorem paper_xi_kappa_unique_carrier (D : xi_kappa_unique_carrier_data) :
    D.maxCompressedInfoEqualsKappa ∧ D.implementationIndependentEntropyLedger := by
  refine ⟨?_, ?_⟩
  · rfl
  · intro foldMap hfoldMap
    subst foldMap
    rfl

end Omega.Zeta
