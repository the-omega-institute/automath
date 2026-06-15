local core = require("core")
local t = fkst.test

local function proposal(extra)
  local value = {
    target = "T-43",
    title = "Source replay task",
    objective = "Audit the candidate and separate confirmed facts from missing source obligations.",
    expected_artifact = "A source-obligation ledger and claim-state JSON record.",
    source_refs = { "tools/community-outreach/RESEARCH_BOARD.md" },
  }
  for key, field in pairs(extra or {}) do
    value[key] = field
  end
  return value
end

return {
  test_validate_proposal_accepts_open_problem_target = function()
    local parsed = assert(core.validate_proposal(proposal()))

    t.eq(parsed.target, "T-43")
    t.eq(parsed.artifact_kind, "claim-state")
    t.eq(parsed.public_impact, false)
  end,

  test_validate_proposal_accepts_sair_public_impact_target = function()
    local parsed = assert(core.validate_proposal(proposal({
      target = "SAIR-EQT2",
      artifact_kind = "sair-solver-submission",
      public_impact = true,
    })))

    t.eq(parsed.target, "SAIR-EQT2")
    t.eq(parsed.artifact_kind, "sair-solver-submission")
    t.eq(parsed.public_impact, true)
  end,

  test_validate_proposal_rejects_unknown_target_and_artifact = function()
    local parsed, err = core.validate_proposal(proposal({ target = "RH" }))
    t.is_nil(parsed)
    t.is_true(tostring(err):find("target", 1, true) ~= nil)

    parsed, err = core.validate_proposal(proposal({ artifact_kind = "paper" }))
    t.is_nil(parsed)
    t.is_true(tostring(err):find("artifact_kind", 1, true) ~= nil)
  end,

  test_consensus_proposal_id_is_path_like_and_bounded = function()
    local parsed = assert(core.validate_proposal(proposal({
      title = "Prepare SAIR Equational Theories Stage 2 solver v4",
      target = "SAIR-EQT2",
    })))
    local proposal_id = core.consensus_proposal_id(parsed)

    t.eq(proposal_id, "omega-open-problem/SAIR-EQT2/prepare-sair-equational-theories-stage-2-solver-v4")
    t.eq(proposal_id:find(" ", 1, true), nil)
    t.is_true(#proposal_id <= 200)
  end,

  test_consensus_payload_helpers_match_upstream_schema = function()
    local parsed = assert(core.validate_proposal(proposal({
      title = "Prepare SAIR Equational Theories Stage 2 solver v4",
      target = "SAIR-EQT2",
      source_refs = { "lean4/Omega/Folding/Window6EquationalSpectrum.lean" },
    })))
    local proposal_id = core.consensus_proposal_id(parsed)
    local source_ref = core.consensus_source_ref(parsed, nil, proposal_id)

    t.eq(core.consensus_proposal_schema(), "consensus.proposal.v1")
    t.eq(core.consensus_dedup_key(parsed), proposal_id .. "/v1")
    t.eq(source_ref.kind, "repo-path")
    t.eq(source_ref.ref, "lean4/Omega/Folding/Window6EquationalSpectrum.lean")
    t.is_true(core.render_consensus_context(parsed):find("Mathematical truth", 1, true) ~= nil)
  end,

  test_render_consensus_body_names_artifact_rules = function()
    local parsed = assert(core.validate_proposal(proposal({
      artifact_kind = "source-replay-ledger",
      public_impact = true,
    })))
    local body = core.render_consensus_body(parsed)

    t.is_true(body:find("Artifact kind: source-replay-ledger", 1, true) ~= nil)
    t.is_true(body:find("Public impact: true", 1, true) ~= nil)
    t.is_true(body:find("Consensus is not a proof", 1, true) ~= nil)
  end,

  test_validate_consensus_reached_only_accepts_approve = function()
    local parsed = assert(core.validate_consensus_reached({
      decision = "approve",
      proposal_id = "omega-open-problem/T-43/source-replay-task",
      body = "Approved because it creates a ledger.",
      dedup_key = "d1",
    }))

    t.eq(parsed.proposal_id, "omega-open-problem/T-43/source-replay-task")
    t.eq(parsed.dedup_key, "d1")

    local rejected = core.validate_consensus_reached({
      decision = "reject",
      proposal_id = "omega-open-problem/T-43/source-replay-task",
      body = "No.",
    })
    t.is_nil(rejected)
  end,

  test_render_artifact_task_forbids_consensus_as_truth = function()
    local body = core.render_artifact_task({
      proposal_id = "omega-open-problem/T-43/source-replay-task",
      dedup_key = "d1",
      body = "Approved.",
    })

    t.is_true(body:find("Do not record mathematical", 1, true) ~= nil)
    t.is_true(body:find("route-refutation", 1, true) ~= nil)
  end,

  test_render_repo_artifact_for_sair_claim_state = function()
    local artifact = core.render_repo_artifact({
      proposal_id = "omega-open-problem/SAIR-EQT2/prepare-sair-equational-theories-stage-2-solver-v4",
      dedup_key = "consensus:omega-open-problem/SAIR-EQT2/prepare-sair-equational-theories-stage-2-solver-v4/v1",
      body = "Approved.",
    })

    t.eq(artifact.schema, "omega.repo_artifact.v1")
    t.eq(artifact.path, "tools/fkst-open-problem/artifacts/sair-eqt2/claim_state.jsonl")
    t.is_true(artifact.content:find("sair-eqt2-window6-fin21-certificate", 1, true) ~= nil)
    t.is_true(artifact.content:find("paper_window6_fin21_facts_certificate", 1, true) ~= nil)
    t.is_true(artifact.content:find("FKST consensus as mathematical proof", 1, true) ~= nil)
  end,
}
