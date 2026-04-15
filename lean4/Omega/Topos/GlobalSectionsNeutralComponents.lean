import Mathlib.Tactic
import Omega.Topos.TerminalFibreNeutrality

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for global sections versus neutral component
    gerbes in `2026_conservative_extension_chain_state_forcing_apal`.
    prop:global-sections-vs-neutral-components -/
theorem paper_gluing_failure_global_sections_vs_neutral_components
    {Branch : Type*}
    (hasGlobalSection : Prop)
    (Visible : Branch → Prop)
    (terminalFibreNonempty neutral : Branch → Prop)
    (hSec : hasGlobalSection ↔ ∃ v, Visible v ∧ terminalFibreNonempty v)
    (hNeutral : ∀ v, Visible v → (terminalFibreNonempty v ↔ neutral v)) :
    (hasGlobalSection ↔ ∃ v, Visible v ∧ terminalFibreNonempty v) ∧
      (hasGlobalSection ↔ ∃ v, Visible v ∧ neutral v) := by
  refine ⟨hSec, ?_⟩
  constructor
  · intro hGlobal
    rcases hSec.mp hGlobal with ⟨v, hv, hTerminal⟩
    exact ⟨v, hv, (hNeutral v hv).mp hTerminal⟩
  · intro hGlobal
    rcases hGlobal with ⟨v, hv, hNeutralV⟩
    exact hSec.mpr ⟨v, hv, (hNeutral v hv).mpr hNeutralV⟩

end Omega.Topos
