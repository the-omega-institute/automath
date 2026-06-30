local M = {}

local max_text = 6000
local function shell_single_quote(value)
  return "'" .. tostring(value or ""):gsub("'", "'\"'\"'") .. "'"
end

function M.consensus_proposal_schema()
  return "consensus.proposal.v1"
end

local function trim(value)
  return tostring(value or ""):gsub("^%s+", ""):gsub("%s+$", "")
end

local function bounded_string(value, limit)
  return type(value) == "string" and value ~= "" and #value <= limit
end

local function json_string(value)
  local text = tostring(value or "")
  text = text:gsub("\\", "\\\\")
  text = text:gsub("\"", "\\\"")
  text = text:gsub("\n", "\\n")
  text = text:gsub("\r", "\\r")
  text = text:gsub("\t", "\\t")
  return "\"" .. text .. "\""
end

function M.validate_proposal(payload)
  if type(payload) ~= "table" then
    return nil, "payload must be a table"
  end
  local target = trim(payload.target)
  if target ~= "SAIR-EQT2" then
    return nil, "target must be SAIR-EQT2"
  end
  local title = trim(payload.title)
  if not bounded_string(title, 240) then
    return nil, "title is required and must be <= 240 bytes"
  end
  local objective = trim(payload.objective)
  if not bounded_string(objective, max_text) then
    return nil, "objective is required and must be <= 6000 bytes"
  end
  local expected = trim(payload.expected_artifact)
  if not bounded_string(expected, 1200) then
    return nil, "expected_artifact is required and must be <= 1200 bytes"
  end
  local artifact_kind = trim(payload.artifact_kind)
  if artifact_kind ~= "sair-solver-submission" and artifact_kind ~= "claim-state" then
    return nil, "artifact_kind must be sair-solver-submission or claim-state"
  end
  return {
    target = target,
    title = title,
    objective = objective,
    expected_artifact = expected,
    artifact_kind = artifact_kind,
    public_impact = payload.public_impact == true,
    source_refs = type(payload.source_refs) == "table" and payload.source_refs or {},
  }, nil
end

function M.consensus_proposal_id(proposal)
  local title = proposal.title:lower():gsub("[^a-z0-9]+", "-"):gsub("^%-+", ""):gsub("%-+$", "")
  if title == "" then
    title = "proposal"
  end
  if #title > 80 then
    title = title:sub(1, 80):gsub("%-+$", "")
  end
  return "omega-sair-eqt2/SAIR-EQT2/" .. title
end

function M.consensus_dedup_key(proposal)
  return M.consensus_proposal_id(proposal) .. "/v1"
end

function M.consensus_source_ref(proposal, event_source_ref, proposal_id)
  if type(event_source_ref) == "table" and bounded_string(event_source_ref.kind, 200)
    and bounded_string(event_source_ref.ref, 200) then
    return event_source_ref
  end
  if type(proposal.source_refs) == "table" and bounded_string(proposal.source_refs[1], 200) then
    return {
      kind = "repo-path",
      ref = proposal.source_refs[1],
    }
  end
  return {
    kind = "omega-sair-eqt2",
    ref = proposal_id,
  }
end

function M.render_consensus_context(_)
  return table.concat({
    "This is a SAIR-EQT2-only FKST routing proposal.",
    "Use FKST consensus only to decide whether the task should produce a durable artifact.",
    "Mathematical truth must remain in Lean, replay scripts, source ledgers, or claim-state metadata.",
    "Keep solver and certificate claims separate from solved-conjecture claims.",
  }, "\n")
end

function M.render_consensus_body(proposal)
  local refs = {}
  for _, ref in ipairs(proposal.source_refs or {}) do
    table.insert(refs, "- " .. tostring(ref))
  end
  if #refs == 0 then
    table.insert(refs, "- none supplied")
  end
  return table.concat({
    "SAIR-EQT2 proposal.",
    "",
    "Target: " .. proposal.target,
    "Title: " .. proposal.title,
    "",
    "Objective:",
    proposal.objective,
    "",
    "Expected durable artifact:",
    proposal.expected_artifact,
    "",
    "Artifact kind: " .. proposal.artifact_kind,
    "Public impact: " .. tostring(proposal.public_impact == true),
    "",
    "Source references:",
    table.concat(refs, "\n"),
    "",
    "Acceptance rule:",
    "Approve only if the proposal can produce a durable repository artifact. Consensus is not a proof.",
  }, "\n")
end

function M.validate_consensus_reached(payload)
  if type(payload) ~= "table" then
    return nil, "payload must be a table"
  end
  if payload.decision ~= "approve" then
    return nil, "decision is not approve"
  end
  local proposal_id = trim(payload.proposal_id)
  if proposal_id:find("omega-sair-eqt2/SAIR-EQT2/", 1, true) ~= 1 then
    return nil, "proposal_id must be omega-sair-eqt2/SAIR-EQT2 scoped"
  end
  local body = trim(payload.body)
  if not bounded_string(body, max_text) then
    return nil, "body is required and must be <= 6000 bytes"
  end
  return {
    proposal_id = proposal_id,
    body = body,
    dedup_key = trim(payload.dedup_key),
    source_ref = payload.source_ref,
  }, nil
end

function M.render_artifact_task(consensus)
  return table.concat({
    "Approved SAIR-EQT2 FKST artifact task.",
    "",
    "Proposal: " .. consensus.proposal_id,
    "Dedup: " .. consensus.dedup_key,
    "",
    "Consensus body:",
    consensus.body,
    "",
    "Required output:",
    "Create or update the durable SAIR-EQT2 repository artifact only. Do not",
    "record mathematical truth as agent consensus. If evidence is incomplete,",
    "produce a blocked claim-state record rather than a theorem claim.",
  }, "\n")
end

function M.validate_consensus_converge(payload)
  if type(payload) ~= "table" then
    return nil, "payload must be a table"
  end
  if payload.schema ~= "consensus.consensus_converge.v1" then
    return nil, "unsupported converge schema"
  end
  local proposal_id = trim(payload.proposal_id)
  if proposal_id:find("omega-sair-eqt2/SAIR-EQT2/", 1, true) ~= 1 then
    return nil, "proposal_id must be omega-sair-eqt2/SAIR-EQT2 scoped"
  end
  local question = trim(payload.narrowed_question)
  if not bounded_string(question, 2000) then
    return nil, "narrowed_question is required and must be <= 2000 bytes"
  end
  return {
    proposal_id = proposal_id,
    dedup_key = trim(payload.dedup_key),
    narrowed_question = question,
    angle_digests = type(payload.angle_digests) == "table" and payload.angle_digests or {},
    source_ref = payload.source_ref,
  }, nil
end

local function render_angle_digests(digests)
  local lines = {}
  for _, item in ipairs(digests or {}) do
    if type(item) == "table" then
      table.insert(lines, "- " .. trim(item.angle) .. ": " .. trim(item.verdict) .. " - " .. trim(item.digest))
    end
  end
  if #lines == 0 then
    return "- none"
  end
  return table.concat(lines, "\n")
end

function M.render_converge_artifact_task(converge)
  return {
    schema = "omega.artifact_task.v1",
    proposal_id = converge.proposal_id,
    dedup_key = converge.dedup_key,
    body = table.concat({
      "SAIR-EQT2 FKST consensus convergence diagnostic.",
      "",
      "Proposal: " .. converge.proposal_id,
      "Dedup: " .. converge.dedup_key,
      "",
      "Consensus did not reach approve/reject. This is not a mathematical fact.",
      "Record a diagnostic artifact instead of retrying into dead letter.",
      "",
      "Narrowed question:",
      converge.narrowed_question,
      "",
      "Angle digests:",
      render_angle_digests(converge.angle_digests),
    }, "\n"),
    source_ref = converge.source_ref,
  }
end

function M.validate_artifact_task(payload)
  if type(payload) ~= "table" then
    return nil, "payload must be a table"
  end
  if payload.schema ~= "omega.artifact_task.v1" then
    return nil, "unsupported artifact task schema"
  end
  local proposal_id = trim(payload.proposal_id)
  if proposal_id:find("omega-sair-eqt2/SAIR-EQT2/", 1, true) ~= 1 then
    return nil, "proposal_id must be omega-sair-eqt2/SAIR-EQT2 scoped"
  end
  local body = trim(payload.body)
  if not bounded_string(body, max_text) then
    return nil, "body is required and must be <= 6000 bytes"
  end
  return {
    proposal_id = proposal_id,
    dedup_key = trim(payload.dedup_key),
    body = body,
    source_ref = payload.source_ref,
  }, nil
end

function M.repo_artifact_path(_)
  return "tools/fkst-open-problem/artifacts/sair-eqt2/claim_state.jsonl"
end

function M.research_artifact_path(_)
  return "tools/fkst-open-problem/artifacts/sair-eqt2/research_run.jsonl"
end

function M.render_repo_artifact_content(task)
  local proposal = json_string(task.proposal_id)
  local dedup = json_string(task.dedup_key)
  local is_converge = task.body:find("FKST consensus convergence diagnostic", 1, true) ~= nil
  if is_converge then
    local diagnostic = json_string(task.body)
    return table.concat({
      '{"schema":"omega.claim_state.v1","target":"SAIR-EQT2","claim_id":"sair-eqt2-fkst-convergence-diagnostic","state":"fkst-converge-diagnostic","public_impact":false,'
        .. '"summary":"FKST consensus did not reach approve/reject during SAIR-EQT2 dogfood; this is an automation diagnostic, not a mathematical claim.",'
        .. '"must_not_claim":["FKST consensus as mathematical proof","SAIR-EQT2 submission approved","new theorem beyond cited Lean anchors"],'
        .. '"diagnostic":' .. diagnostic .. ','
        .. '"fkst_proposal_id":' .. proposal .. ',"fkst_dedup_key":' .. dedup .. '}',
      "",
    }, "\n")
  end
  return table.concat({
    '{"schema":"omega.claim_state.v1","target":"SAIR-EQT2","claim_id":"sair-eqt2-window6-fin21-certificate","state":"lean-anchor-present","public_impact":true,'
      .. '"summary":"Window-6 Fin 21 rectangular-band certificate gives deterministic satisfied/refuted ETP facts and spectrum counts; this is a certificate-layer contribution, not a solved-conjecture claim.",'
      .. '"must_not_claim":["general Equational Theories solved","new theorem beyond cited Lean/checker/source artifacts","FKST consensus as mathematical proof","SAIR-EQT2 submission accepted"],'
      .. '"lean_refs":["lean4/Omega/EA/Window6CountermodelCertificate.lean#paper_window6_fin21_facts_certificate","lean4/Omega/EA/Window6CountermodelCertificate.lean#paper_window6_equational_spectrum","lean4/Omega/Folding/Window6EquationalSpectrum.lean#paper_window6_equational_spectrum"],'
      .. '"script_refs":["theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/scripts/equational_theory/audit_window6_current.py","theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/scripts/equational_theory/coefficient_analysis.py"],'
      .. '"fkst_proposal_id":' .. proposal .. ',"fkst_dedup_key":' .. dedup .. '}',
    '{"schema":"omega.claim_state.v1","target":"SAIR-EQT2","claim_id":"sair-eqt2-submission-boundary","state":"submission-prep","public_impact":true,'
      .. '"summary":"Use Omega/Automath finite-magma and Lean certificate artifacts as a deterministic checker layer before LLM escalation for SAIR Stage 2 participation.",'
      .. '"must_not_claim":["general Equational Theories solved","new theorem beyond cited Lean anchors","FKST consensus as mathematical proof"],'
      .. '"next_artifact":"solver submission shard plus public Contributor Network description",'
      .. '"fkst_proposal_id":' .. proposal .. ',"fkst_dedup_key":' .. dedup .. '}',
    "",
  }, "\n")
end

function M.render_repo_artifact(task)
  return {
    schema = "omega.repo_artifact.v1",
    proposal_id = task.proposal_id,
    dedup_key = task.dedup_key,
    path = M.repo_artifact_path(task),
    content = M.render_repo_artifact_content(task),
    source_ref = task.source_ref,
  }
end

function M.validate_research_task(payload)
  if type(payload) ~= "table" then
    return nil, "payload must be a table"
  end
  if trim(payload.target) ~= "SAIR-EQT2" then
    return nil, "target must be SAIR-EQT2"
  end
  local run_id = trim(payload.run_id)
  if not bounded_string(run_id, 200) then
    return nil, "run_id is required and must be <= 200 bytes"
  end
  local objective = trim(payload.objective)
  if not bounded_string(objective, max_text) then
    return nil, "objective is required and must be <= 6000 bytes"
  end
  local repo_root = trim(payload.repo_root)
  if not bounded_string(repo_root, 1000) then
    return nil, "repo_root is required"
  end
  return {
    target = "SAIR-EQT2",
    run_id = run_id,
    objective = objective,
    repo_root = repo_root,
    source_refs = type(payload.source_refs) == "table" and payload.source_refs or {},
  }, nil
end

function M.render_research_candidate_prompt(task)
  local refs = {}
  for _, ref in ipairs(task.source_refs or {}) do
    table.insert(refs, "- " .. tostring(ref))
  end
  if #refs == 0 then
    table.insert(refs, "- none supplied")
  end
  return table.concat({
    "You are inside an FKST dogfood run for exactly one target: SAIR-EQT2.",
    "Do not discuss Israel, Tolmetes, or general open-problem automation.",
    "FKST consensus is not mathematical proof. Propose one small research/checker action only.",
    "The action must be checkable by local scripts or Lean/source replay, not by LLM agreement.",
    "",
    "Preferred sharded linear-magma actions:",
    "- Use action_id linear-magma-shard-vars<K>-p<P> for small K and allowed P in {2,3,5,7,11,13,17,19,89,233}.",
    "- For these actions, set checker_plan to run linear_magma_search.py with --selected-primes P and --max-vars-selected K.",
    "- Set expected_artifact to a JSON checker row with selected_prime_results for P, bounded baseline evidence, and brute-force sanity status.",
    "- Do not propose out-of-allowlist prime shards; they are routed to baseline coefficient_analysis with a dispatch rejection marker.",
    "",
    "Objective:",
    task.objective,
    "",
    "Available source refs:",
    table.concat(refs, "\n"),
    "",
    "Return exactly one JSON object and no markdown:",
    "{",
    '  "action_id": "short-kebab-case-id",',
    '  "hypothesis": "what this action may learn, stated conservatively",',
    '  "checker_plan": "which local checker/script should validate it",',
    '  "expected_artifact": "what evidence should be written if the checker runs"',
    "}",
  }, "\n")
end

function M.codex_advisory_enabled_cmd()
  return 'printf %s "${FKST_SAIR_EQT2_CODEX:-0}"'
end

function M.research_codex_opts(prompt, repo_root)
  return {
    prompt = prompt,
    worktree = repo_root,
    sandbox = "read-only",
    timeout = 900,
  }
end

local function portfolio_candidate(action_id, hypothesis, checker_plan, expected_artifact, frequency)
  return {
    action_id = action_id,
    state = "candidate-generated",
    hypothesis = hypothesis,
    checker_plan = checker_plan,
    expected_artifact = expected_artifact,
    frequency = frequency or "default",
    source = "deterministic-portfolio",
  }
end

function M.research_portfolio_candidates(_)
  return {
    portfolio_candidate(
      "coefficient-analysis-baseline",
      "Check the local 4694-equation coefficient-analysis baseline before any SAIR-EQT2 submission claim.",
      "Run coefficient_analysis.py --no-scan and summarize the deterministic equation-count and coefficient bounds.",
      "Checker-backed research_run row with equation_count=4694 and matches_expected_count=true.",
      "default"
    ),
    portfolio_candidate(
      "claim-boundary-audit",
      "Audit SAIR-EQT2 artifacts for target scope and prohibited proof/submission claims.",
      "Parse claim_state.jsonl and research_run.jsonl; fail if target is not SAIR-EQT2 or if accepted/submitted/proof claims appear outside must_not_claim boundaries.",
      "Boundary audit row proving the automation output remains claim-safe.",
      "default"
    ),
    portfolio_candidate(
      "linear-magma-smoke",
      "Run a bounded linear magma smoke check to confirm the search path still loads public ETP equations and has no brute-force mismatch.",
      "Run linear_magma_search.py only with a small timeout/bounded configuration; record timeout as a non-mathematical scheduling finding.",
      "Smoke-check row with loaded equation source, partial progress, timeout, or sanity status.",
      "low-frequency"
    ),
    portfolio_candidate(
      "linear-magma-shard-vars1-p13",
      "Run a bounded p=13 linear-magma shard over local one-variable ETP laws to produce pattern evidence.",
      "Run linear_magma_search.py against the local 4694-equation generator with max_vars_p13=1 and bounded baseline primes.",
      "Checker-backed search row with source, equation_count_total, p=13 pattern count, anti-implication baseline count, and sanity status.",
      "default"
    ),
    portfolio_candidate(
      "linear-magma-shard-vars2-p13",
      "Run a bounded p=13 linear-magma shard over local two-variable ETP laws to produce larger pattern evidence.",
      "Run linear_magma_search.py against the local 4694-equation generator with max_vars_p13=2 and bounded baseline primes.",
      "Checker-backed search row with two-variable p=13 pattern count and bounded baseline anti-implication count.",
      "default"
    ),
    portfolio_candidate(
      "linear-magma-shard-vars1-p89",
      "Run a bounded p=89 linear-magma shard over local one-variable ETP laws to compare prime-field pattern evidence.",
      "Run linear_magma_search.py against the local 4694-equation generator with max_vars_p89=1 and bounded baseline primes.",
      "Checker-backed search row with p=89 one-variable pattern evidence and bounded baseline comparison.",
      "default"
    ),
    portfolio_candidate(
      "linear-magma-shard-vars2-p89",
      "Run a bounded p=89 linear-magma shard over local two-variable ETP laws to compare larger prime-field pattern evidence.",
      "Run linear_magma_search.py against the local 4694-equation generator with max_vars_p89=2 and bounded baseline primes.",
      "Checker-backed search row with p=89 two-variable pattern evidence and bounded baseline comparison.",
      "default"
    ),
  }
end

local function parse_json_object(text)
  local candidate = tostring(text or ""):match("(%b{})")
  if candidate == nil then
    return nil, "no JSON object found"
  end
  local ok, decoded = pcall(json.decode, candidate)
  if not ok then
    return nil, tostring(decoded)
  end
  if type(decoded) ~= "table" then
    return nil, "decoded JSON is not an object"
  end
  return decoded, nil
end

function M.parse_research_candidate(stdout)
  local decoded, err = parse_json_object(stdout)
  if decoded == nil then
    return {
      action_id = "codex-output-unparseable",
      state = "candidate-generated",
      hypothesis = "Codex did not return parseable JSON; checker should record the failure and continue.",
      checker_plan = "Record parse failure as an automation artifact; do not claim mathematical progress.",
      expected_artifact = "blocked candidate record with Codex output excerpt",
      parse_error = tostring(err),
      raw_excerpt = tostring(stdout or ""):sub(1, 1200),
    }
  end
  local action_id = trim(decoded.action_id):lower():gsub("[^a-z0-9%-]+", "-"):gsub("^%-+", ""):gsub("%-+$", "")
  if action_id == "" then
    action_id = "codex-candidate"
  end
  return {
    action_id = action_id:sub(1, 80),
    state = "candidate-generated",
    hypothesis = trim(decoded.hypothesis):sub(1, 1200),
    checker_plan = trim(decoded.checker_plan):sub(1, 1200),
    expected_artifact = trim(decoded.expected_artifact):sub(1, 1200),
    raw_excerpt = tostring(stdout or ""):sub(1, 1200),
  }
end

function M.validate_candidate_search(payload)
  if type(payload) ~= "table" then
    return nil, "payload must be a table"
  end
  if trim(payload.target) ~= "SAIR-EQT2" then
    return nil, "target must be SAIR-EQT2"
  end
  local run_id = trim(payload.run_id)
  if not bounded_string(run_id, 200) then
    return nil, "run_id is required"
  end
  local candidate = payload.candidate
  if type(candidate) ~= "table" then
    return nil, "candidate must be a table"
  end
  return {
    target = "SAIR-EQT2",
    run_id = run_id,
    repo_root = trim(payload.repo_root),
    candidate = candidate,
    codex_exit_code = tonumber(payload.codex_exit_code) or -1,
    codex_error_class = trim(payload.codex_error_class),
    source_ref = payload.source_ref,
  }, nil
end

function M.render_candidate_json(candidate)
  return table.concat({
    "{",
    '"action_id":' .. json_string(candidate.action_id) .. ",",
    '"state":' .. json_string(candidate.state) .. ",",
    '"hypothesis":' .. json_string(candidate.hypothesis) .. ",",
    '"checker_plan":' .. json_string(candidate.checker_plan) .. ",",
    '"expected_artifact":' .. json_string(candidate.expected_artifact) .. ",",
    '"parse_error":' .. json_string(candidate.parse_error) .. ",",
    '"raw_excerpt":' .. json_string(candidate.raw_excerpt) .. ",",
    '"frequency":' .. json_string(candidate.frequency) .. ",",
    '"source":' .. json_string(candidate.source),
    "}",
  }, "")
end

function M.research_checker_cmd(candidate_search)
  local script = "tools/fkst-open-problem/scripts/sair_eqt2_research_check.py"
  local candidate_json = M.render_candidate_json(candidate_search.candidate)
  return "python3 " .. shell_single_quote(script)
    .. " --candidate-json " .. shell_single_quote(candidate_json)
end

function M.validate_checker_result(payload)
  if type(payload) ~= "table" then
    return nil, "payload must be a table"
  end
  if trim(payload.target) ~= "SAIR-EQT2" then
    return nil, "target must be SAIR-EQT2"
  end
  local run_id = trim(payload.run_id)
  if not bounded_string(run_id, 200) then
    return nil, "run_id is required"
  end
  local checker = payload.checker
  if type(checker) ~= "table" then
    return nil, "checker must be a table"
  end
  return {
    target = "SAIR-EQT2",
    run_id = run_id,
    candidate = type(payload.candidate) == "table" and payload.candidate or {},
    checker = checker,
    source_ref = payload.source_ref,
  }, nil
end

local function json_object_or_string(value)
  if type(value) == "table" then
    return json.encode(value)
  end
  local text = tostring(value or "")
  local ok, decoded = pcall(json.decode, text)
  if ok and type(decoded) == "table" then
    return text
  end
  return json_string(text)
end

function M.render_research_artifact_content(result)
  local checker_summary = result.checker.summary or {}
  return table.concat({
    '{"schema":"omega.research_run.v1","target":"SAIR-EQT2","run_id":' .. json_string(result.run_id)
      .. ',"state":"checker-ran","claim_scope":"automation-research-evidence-not-proof",'
      .. '"candidate_action_id":' .. json_string(result.candidate.action_id)
      .. ',"candidate_hypothesis":' .. json_string(result.candidate.hypothesis)
      .. ',"candidate_source":' .. json_string(result.candidate.source)
      .. ',"candidate_frequency":' .. json_string(result.candidate.frequency)
      .. ',"checker_name":' .. json_string(result.checker.checker_name)
      .. ',"checker_exit_code":' .. tostring(tonumber(result.checker.exit_code) or -1)
      .. ',"checker_status":' .. json_string(result.checker.status)
      .. ',"summary":' .. json_string(checker_summary.text)
      .. ',"evidence":' .. json_object_or_string(result.checker.evidence)
      .. ',"must_not_claim":["FKST consensus as mathematical proof","SAIR-EQT2 submission accepted","new theorem beyond Lean/checker/source artifacts"]}',
    "",
  }, "\n")
end

function M.render_research_artifact(result)
  return {
    schema = "omega.repo_artifact.v1",
    proposal_id = "omega-sair-eqt2/SAIR-EQT2/research-run-" .. result.run_id,
    dedup_key = "omega-sair-eqt2/research/" .. result.run_id,
    path = M.research_artifact_path(result),
    content = M.render_research_artifact_content(result),
    source_ref = result.source_ref,
  }
end

return M
