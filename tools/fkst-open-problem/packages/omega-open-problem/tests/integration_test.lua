local t = fkst.test

local function run_intake(payload)
  return t.run_department("departments/proposal_intake/main.lua", {
    queue = "omega_proposal",
    payload = payload,
    source_ref = {
      kind = "manual",
      ref = "omega-open-problem-test",
    },
  })
end

local function run_artifact(payload)
  return t.run_department("departments/artifact_task/main.lua", {
    queue = "consensus.consensus_reached",
    payload = payload,
  })
end

return {
  test_seed_t43_raises_open_problem_proposal = function()
    local result = t.run_department("departments/seed_t43/main.lua", {
      queue = "omega_seed_tick",
      payload = {
        raiser = "seed",
      },
    })

    t.eq(result.exit_code, 0)
    t.eq(#result.raises, 1)
    t.eq(result.raises[1].queue, "omega_proposal")
    t.eq(result.raises[1].payload.target, "T-43")
    t.is_true(result.raises[1].payload.title:find("Source-replay A5 same-W", 1, true) ~= nil)
  end,

  test_seed_sair_raises_public_impact_proposal = function()
    local result = t.run_department("departments/seed_sair_stage2/main.lua", {
      queue = "omega_sair_stage2_tick",
      payload = {
        raiser = "sair_stage2",
      },
    })

    t.eq(result.exit_code, 0)
    t.eq(#result.raises, 1)
    t.eq(result.raises[1].queue, "omega_proposal")
    t.eq(result.raises[1].payload.target, "SAIR-EQT2")
    t.eq(result.raises[1].payload.public_impact, true)
  end,

  test_proposal_intake_raises_consensus_proposal = function()
    local result = run_intake({
      target = "SAIR-EQT2",
      title = "Prepare SAIR Equational Theories Stage 2 solver v4",
      artifact_kind = "sair-solver-submission",
      public_impact = true,
      objective = "Prepare a deterministic certificate-layer solver update.",
      expected_artifact = "A solver submission shard and public description.",
    })

    t.eq(result.exit_code, 0)
    t.eq(#result.raises, 1)
    t.eq(result.raises[1].queue, "consensus.proposal")
    t.eq(result.raises[1].payload.schema, "consensus.proposal.v1")
    t.eq(result.raises[1].payload.verdict_mode, "gate")
    t.eq(result.raises[1].payload.proposal_id, "omega-open-problem/SAIR-EQT2/prepare-sair-equational-theories-stage-2-solver-v4")
    t.eq(result.raises[1].payload.dedup_key, "omega-open-problem/SAIR-EQT2/prepare-sair-equational-theories-stage-2-solver-v4/v1")
    t.eq(result.raises[1].payload.source_ref.kind, "manual")
    t.is_true(result.raises[1].payload.body:find("Public impact: true", 1, true) ~= nil)
    t.is_true(result.raises[1].payload.context:find("Mathematical truth", 1, true) ~= nil)
  end,

  test_artifact_task_ignores_rejected_consensus = function()
    local result = run_artifact({
      decision = "reject",
      proposal_id = "omega-open-problem/T-43/source-replay-task",
      body = "Rejected.",
    })

    t.eq(result.exit_code, 0)
    t.eq(#result.raises, 0)
  end,

  test_artifact_task_raises_durable_task_on_approval = function()
    local result = run_artifact({
      decision = "approve",
      proposal_id = "omega-open-problem/T-43/source-replay-task",
      body = "Approved because it creates a source ledger.",
      dedup_key = "d1",
      source_ref = {
        kind = "github",
        ref = "the-omega-institute/automath#issue/1",
      },
    })

    t.eq(result.exit_code, 0)
    t.eq(#result.raises, 1)
    t.eq(result.raises[1].queue, "omega_artifact_task")
    t.eq(result.raises[1].payload.schema, "omega.artifact_task.v1")
    t.eq(result.raises[1].payload.source_ref.kind, "github")
    t.is_true(result.raises[1].payload.body:find("Consensus is not a proof", 1, true) == nil)
    t.is_true(result.raises[1].payload.body:find("Do not record mathematical", 1, true) ~= nil)
  end,
}
