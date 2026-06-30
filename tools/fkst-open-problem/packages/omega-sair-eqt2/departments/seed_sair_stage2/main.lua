local M = {}

M.spec = {
  consumes = { "omega_sair_stage2_tick" },
  produces = { "omega_proposal", "omega_research_task", "omega_codex_research_task" },
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
  raise("omega_research_task", {
    target = "SAIR-EQT2",
    run_id = "sair-eqt2-research-v1",
    repo_root = "/Users/lexa/Desktop/lexa/omega/automath-outreach",
    objective = table.concat({
      "Use Codex to propose one small SAIR-EQT2 checker/search action, then",
      "run deterministic local equational-theory scripts and record only",
      "evidence backed by checker output. Do not claim proof or submission",
      "success from FKST consensus or Codex text.",
    }, " "),
    source_refs = {
      "lean4/Omega/Folding/Window6EquationalSpectrum.lean",
      "lean4/Omega/EA/Window6CountermodelCertificate.lean",
      "theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/scripts/equational_theory/coefficient_analysis.py",
      "theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/scripts/equational_theory/linear_magma_search.py",
    },
  })
  raise("omega_codex_research_task", {
    target = "SAIR-EQT2",
    run_id = "sair-eqt2-codex-advisory-v1",
    repo_root = "/Users/lexa/Desktop/lexa/omega/automath-outreach",
    objective = table.concat({
      "Optionally ask Codex for one SAIR-EQT2 research/checker suggestion.",
      "This lane is disabled unless FKST_SAIR_EQT2_CODEX=1 because it may",
      "send repository context to the configured Codex backend.",
    }, " "),
    source_refs = {
      "lean4/Omega/Folding/Window6EquationalSpectrum.lean",
      "lean4/Omega/EA/Window6CountermodelCertificate.lean",
      "theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/scripts/equational_theory/",
    },
  })
end

return M
