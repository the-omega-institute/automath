import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-multichannel-witness-kappa-or-anom`. A genuine visible-channel
negative-square resonance produces the finite witness, while failure of strictification produces
the anomaly witness. -/
theorem paper_xi_multichannel_witness_kappa_or_anom {Pi : Type*} (sqNeg : Pi → ℕ)
    (finiteWitness strictification anomalyWitness : Prop)
    (hRes : (∃ π, 0 < sqNeg π) → finiteWitness)
    (hAnom : ¬ strictification → anomalyWitness) :
    ((∃ π, 0 < sqNeg π) ∨ ¬ strictification) → finiteWitness ∨ anomalyWitness := by
  intro h
  rcases h with hResonance | hStrictification
  · exact Or.inl (hRes hResonance)
  · exact Or.inr (hAnom hStrictification)

end Omega.Zeta
