import Mathlib.Tactic

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the `2r_m`-moment Prony--Hankel reconstruction package.
    thm:pom-fiber-spectrum-prony-hankel-2r-reconstruction -/
theorem paper_pom_fiber_spectrum_prony_hankel_2r_reconstruction
    (minimalRecurrence uniqueMonicRecurrencePoly atomRecovery multiplicityRecovery : Prop) :
    minimalRecurrence ->
      (minimalRecurrence -> uniqueMonicRecurrencePoly) ->
      (uniqueMonicRecurrencePoly -> atomRecovery) ->
      (atomRecovery -> multiplicityRecovery) ->
      minimalRecurrence ∧ uniqueMonicRecurrencePoly ∧ atomRecovery ∧ multiplicityRecovery := by
  intro hMinimal hUnique hAtom hMultiplicity
  have hMonic : uniqueMonicRecurrencePoly := hUnique hMinimal
  have hAtoms : atomRecovery := hAtom hMonic
  have hMult : multiplicityRecovery := hMultiplicity hAtoms
  exact ⟨hMinimal, hMonic, hAtoms, hMult⟩

end Omega.POM
