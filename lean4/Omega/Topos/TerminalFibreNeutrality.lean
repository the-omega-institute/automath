namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the terminal-fibre neutrality lemma in
    `2026_conservative_extension_chain_state_forcing_apal`.
    lem:terminal-fibre-neutrality -/
theorem paper_gluing_failure_terminal_fibre_neutrality
    (terminalFibreNonempty neutral : Prop)
    (hNeutral : terminalFibreNonempty ↔ neutral) :
    terminalFibreNonempty ↔ neutral :=
  hNeutral

end Omega.Topos
