import Mathlib.Data.Fintype.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-endpoint-atom-central-channel-strength`. -/
theorem paper_xi_endpoint_atom_central_channel_strength {ι : Type*} [Fintype ι]
    (atomPositive abelianAlgebra centralMeasure atomCentral : Prop)
    (channelScalar channelNonnegative : ι -> Prop) (hAbelian : abelianAlgebra -> atomCentral)
    (hCentral : centralMeasure -> atomCentral)
    (hSchur : centralMeasure -> ∀ i, channelScalar i ∧ channelNonnegative i) :
    atomPositive ->
      (abelianAlgebra -> atomCentral) ∧
        (centralMeasure -> atomCentral ∧ ∀ i, channelScalar i ∧ channelNonnegative i) := by
  intro _hAtomPositive
  refine ⟨hAbelian, ?_⟩
  intro hCentralMeasure
  exact ⟨hCentral hCentralMeasure, hSchur hCentralMeasure⟩

end Omega.Zeta
