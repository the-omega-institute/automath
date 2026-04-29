import Omega.TypedAddressBiaxialCompletion.PcdimModpFormula

namespace Omega.UnitCirclePhaseArithmetic

open Omega.CircleDimension
open Omega.TypedAddressBiaxialCompletion

/-- Complete-phase ledger wrapper around the typed-address profinite-kernel data. The extra field
records the register-circle dimension used by the chapter-local ledger language. -/
structure CompletePhasePcdimModpData extends TypedAddressPcdimModpData where
  registerCircleDim : Nat
  registerCircleDim_eq_pcdim : registerCircleDim = pcdim

namespace CompletePhasePcdimModpData

/-- The mod-`p` prime supremum read in the complete-phase ledger language. -/
def modpPrimeSup (D : CompletePhasePcdimModpData) : Nat :=
  registerCirclePrimeSup D.primes D.modpDim

end CompletePhasePcdimModpData

open CompletePhasePcdimModpData

/-- Paper label: `prop:unit-circle-complete-phase-pcdim-modp`. -/
theorem paper_unit_circle_complete_phase_pcdim_modp (D : CompletePhasePcdimModpData) :
    D.registerCircleDim = D.modpPrimeSup := by
  calc
    D.registerCircleDim = D.pcdim := D.registerCircleDim_eq_pcdim
    _ = registerCirclePrimeSup D.primes D.modpDim := by
      exact paper_typed_address_biaxial_completion_pcdim_modp D.toTypedAddressPcdimModpData
    _ = D.modpPrimeSup := rfl

end Omega.UnitCirclePhaseArithmetic
