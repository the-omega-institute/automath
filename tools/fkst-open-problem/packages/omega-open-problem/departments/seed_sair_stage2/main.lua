local M = {}

M.spec = {
  consumes = { "omega_sair_stage2_tick" },
  produces = { "omega_proposal" },
  stall_window = "2m",
}

function pipeline(_)
  raise("omega_proposal", {
    target = "SAIR-EQT2",
    title = "Prepare SAIR Equational Theories Stage 2 solver v4",
    artifact_kind = "sair-solver-submission",
    public_impact = true,
    objective = table.concat({
      "Package a public SAIR Stage 2 solver update that uses Omega/Automath",
      "finite-magma and Lean-certificate infrastructure as a deterministic",
      "certificate layer before LLM escalation. The output should be suitable",
      "for official submission and Contributor Network publication.",
    }, " "),
    expected_artifact = table.concat({
      "A solver submission plan or source shard with claim-state metadata,",
      "including exact SAIR track, deterministic certificate routes, known",
      "unsupported cases, and public Contributor Network description.",
    }, " "),
    source_refs = {
      "lean4/Omega/Folding/Window6EquationalSpectrum.lean",
      "lean4/Omega/EA/Window6CountermodelCertificate.lean",
      "theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/scripts/equational_theory/",
    },
  })
end

return M
