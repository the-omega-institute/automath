local t = fkst.test

local function run_seed()
  return t.run_department("departments/seed_sair_stage2/main.lua", {
    queue = "omega_sair_stage2_tick",
    payload = {
      raiser = "sair_stage2",
    },
  })
end

local function run_intake(payload)
  return t.run_department("departments/proposal_intake/main.lua", {
    queue = "omega_proposal",
    payload = payload,
    source_ref = {
      kind = "dogfood",
      ref = "SAIR-EQT2",
    },
  })
end

local function run_artifact_task(payload)
  return t.run_department("departments/artifact_task/main.lua", {
    queue = "consensus.consensus_reached",
    payload = payload,
  })
end

local function run_writer(payload)
  return t.run_department("departments/artifact_writer/main.lua", {
    queue = "omega_artifact_task",
    payload = payload,
  })
end

local function run_converge(payload)
  return t.run_department("departments/converge_diagnostic/main.lua", {
    queue = "consensus.consensus_converge",
    payload = payload,
  })
end

local function run_sink(payload)
  return t.run_department("departments/repo_artifact_sink/main.lua", {
    queue = "omega_repo_artifact",
    payload = payload,
  })
end

local function run_research_candidate(payload)
  return t.run_department("departments/research_candidate/main.lua", {
    queue = "omega_research_task",
    payload = payload,
  })
end

local function run_research_portfolio(payload)
  return t.run_department("departments/research_portfolio/main.lua", {
    queue = "omega_research_task",
    payload = payload,
  })
end

local function run_research_checker(payload)
  return t.run_department("departments/research_checker/main.lua", {
    queue = "omega_candidate_search",
    payload = payload,
  })
end

local function run_research_artifact(payload)
  return t.run_department("departments/research_artifact/main.lua", {
    queue = "omega_checker_result",
    payload = payload,
  })
end

return {
  test_sair_only_pipeline_reaches_repo_artifact = function()
    local seed = run_seed()
    t.eq(seed.exit_code, 0)
    t.eq(#seed.raises, 3)
    t.eq(seed.raises[1].queue, "omega_proposal")
    t.eq(seed.raises[1].payload.target, "SAIR-EQT2")
    t.eq(seed.raises[2].queue, "omega_research_task")
    t.eq(seed.raises[2].payload.target, "SAIR-EQT2")
    t.eq(seed.raises[3].queue, "omega_codex_research_task")
    t.eq(seed.raises[3].payload.target, "SAIR-EQT2")

    local intake = run_intake(seed.raises[1].payload)
    t.eq(intake.exit_code, 0)
    t.eq(#intake.raises, 1)
    t.eq(intake.raises[1].queue, "consensus.proposal")
    t.eq(intake.raises[1].payload.proposal_id, "omega-sair-eqt2/SAIR-EQT2/prepare-sair-equational-theories-stage-2-solver-v4")

    local task = run_artifact_task({
      schema = "consensus.consensus_reached.v1",
      decision = "approve",
      proposal_id = intake.raises[1].payload.proposal_id,
      dedup_key = "consensus:" .. intake.raises[1].payload.dedup_key,
      body = "Approved for local SAIR-EQT2 dogfood.",
      source_ref = intake.raises[1].payload.source_ref,
    })
    t.eq(task.exit_code, 0)
    t.eq(#task.raises, 1)
    t.eq(task.raises[1].queue, "omega_artifact_task")

    local writer = run_writer(task.raises[1].payload)
    t.eq(writer.exit_code, 0)
    t.eq(#writer.raises, 1)
    t.eq(writer.raises[1].queue, "omega_repo_artifact")
    t.eq(writer.raises[1].payload.path, "tools/fkst-open-problem/artifacts/sair-eqt2/claim_state.jsonl")
    t.is_true(writer.raises[1].payload.content:find("SAIR-EQT2", 1, true) ~= nil)
    t.is_true(writer.raises[1].payload.content:find("FKST consensus as mathematical proof", 1, true) ~= nil)

    local sink = run_sink(writer.raises[1].payload)
    t.eq(sink.exit_code, 0)
    t.eq(#sink.raises, 0)
  end,

  test_research_task_runs_codex_candidate_checker_and_artifact = function()
    t.mock_command("printf %s", {
      stdout = "1",
      exit_code = 0,
    })
    t.mock_command("codex exec", {
      stdout = '{"action_id":"coefficient-analysis-baseline","hypothesis":"Check the local coefficient-analysis baseline before any submission claim.","checker_plan":"Run coefficient_analysis.py --no-scan.","expected_artifact":"A checker-backed research_run row."}',
      exit_code = 0,
    })
    t.mock_command("python3 'tools/fkst-open-problem/scripts/sair_eqt2_research_check.py'", {
      stdout = '{"schema":"omega.sair_eqt2.checker_result.v1","target":"SAIR-EQT2","checker_name":"coefficient_analysis.py --no-scan","status":"checked","exit_code":0,"summary":{"text":"Deterministic coefficient analysis generated the standard ETP equation count 4694.","coefficient_analysis":{"equation_count":4694,"matches_expected_count":true}},"evidence":"{\\"equation_count\\":4694}"}',
      exit_code = 0,
    })

    local seed = run_seed()
    local candidate = run_research_candidate(seed.raises[3].payload)
    t.eq(candidate.exit_code, 0)
    t.eq(#candidate.raises, 1)
    t.eq(candidate.raises[1].queue, "omega_candidate_search")
    t.eq(candidate.raises[1].payload.target, "SAIR-EQT2")
    t.eq(candidate.raises[1].payload.candidate.action_id, "coefficient-analysis-baseline")

    local checked = run_research_checker(candidate.raises[1].payload)
    t.eq(checked.exit_code, 0)
    t.eq(#checked.raises, 1)
    t.eq(checked.raises[1].queue, "omega_checker_result")
    t.eq(checked.raises[1].payload.checker.status, "checked")

    local artifact = run_research_artifact(checked.raises[1].payload)
    t.eq(artifact.exit_code, 0)
    t.eq(#artifact.raises, 1)
    t.eq(artifact.raises[1].queue, "omega_repo_artifact")
    t.eq(artifact.raises[1].payload.path, "tools/fkst-open-problem/artifacts/sair-eqt2/research_run.jsonl")
    t.is_true(artifact.raises[1].payload.content:find("automation-research-evidence-not-proof", 1, true) ~= nil)
    t.is_true(artifact.raises[1].payload.content:find("FKST consensus as mathematical proof", 1, true) ~= nil)

    local sink = run_sink(artifact.raises[1].payload)
    t.eq(sink.exit_code, 0)
    t.eq(#sink.raises, 0)
  end,

  test_research_portfolio_fans_out_local_checker_candidates = function()
    local seed = run_seed()
    local portfolio = run_research_portfolio(seed.raises[2].payload)
    t.eq(portfolio.exit_code, 0)
    t.eq(#portfolio.raises, 7)
    t.eq(portfolio.raises[1].queue, "omega_candidate_search")
    t.eq(portfolio.raises[1].payload.target, "SAIR-EQT2")
    t.eq(portfolio.raises[1].payload.candidate.action_id, "coefficient-analysis-baseline")
    t.eq(portfolio.raises[2].payload.candidate.action_id, "claim-boundary-audit")
    t.eq(portfolio.raises[3].payload.candidate.action_id, "linear-magma-smoke")
    t.eq(portfolio.raises[4].payload.candidate.action_id, "linear-magma-shard-vars1-p13")
    t.eq(portfolio.raises[5].payload.candidate.action_id, "linear-magma-shard-vars2-p13")
    t.eq(portfolio.raises[6].payload.candidate.action_id, "linear-magma-shard-vars1-p89")
    t.eq(portfolio.raises[7].payload.candidate.action_id, "linear-magma-shard-vars2-p89")
    t.eq(portfolio.raises[1].payload.candidate.source, "deterministic-portfolio")
  end,

  test_research_candidate_is_codex_opt_in = function()
    t.mock_command("printf %s", {
      stdout = "0",
      exit_code = 0,
    })
    local seed = run_seed()
    local candidate = run_research_candidate(seed.raises[3].payload)
    t.eq(candidate.exit_code, 0)
    t.eq(#candidate.raises, 0)
  end,

  test_converge_becomes_diagnostic_artifact_instead_of_dead_letter = function()
    local converge = run_converge({
      schema = "consensus.consensus_converge.v1",
      proposal_id = "omega-sair-eqt2/SAIR-EQT2/prepare-sair-equational-theories-stage-2-solver-v4",
      dedup_key = "consensus:omega-sair-eqt2/SAIR-EQT2/prepare-sair-equational-theories-stage-2-solver-v4/v1",
      narrowed_question = "Resolve invalid angle outputs.",
      angle_digests = {
        {
          angle = "minimal",
          verdict = "invalid",
          digest = "No parseable angle reply.",
        },
      },
    })
    t.eq(converge.exit_code, 0)
    t.eq(#converge.raises, 1)
    t.eq(converge.raises[1].queue, "omega_artifact_task")
    t.is_true(converge.raises[1].payload.body:find("convergence diagnostic", 1, true) ~= nil)

    local writer = run_writer(converge.raises[1].payload)
    t.eq(writer.exit_code, 0)
    t.eq(#writer.raises, 1)
    t.eq(writer.raises[1].queue, "omega_repo_artifact")
    t.is_true(writer.raises[1].payload.content:find("fkst-converge-diagnostic", 1, true) ~= nil)
    t.is_true(writer.raises[1].payload.content:find("not a mathematical claim", 1, true) ~= nil)

    local sink = run_sink(writer.raises[1].payload)
    t.eq(sink.exit_code, 0)
    t.eq(#sink.raises, 0)
  end,
}
