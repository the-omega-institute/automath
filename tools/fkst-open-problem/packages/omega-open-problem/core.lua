local M = {}

local allowed_targets = {
  ["T-43"] = true,
  ["T-44"] = true,
  ["T-32"] = true,
  ["SAIR-EQT2"] = true,
}

local allowed_artifact_kinds = {
  ["source-replay-ledger"] = true,
  ["route-refutation"] = true,
  ["claim-state"] = true,
  ["audit-manifest"] = true,
  ["sair-solver-submission"] = true,
}

local max_text = 6000

function M.consensus_proposal_schema()
  return "consensus.proposal.v1"
end

local function trim(value)
  return tostring(value or ""):gsub("^%s+", ""):gsub("%s+$", "")
end

local function bounded_string(value, limit)
  return type(value) == "string" and value ~= "" and #value <= limit
end

function M.validate_proposal(payload)
  if type(payload) ~= "table" then
    return nil, "payload must be a table"
  end
  local target = trim(payload.target)
  if not allowed_targets[target] then
    return nil, "target must be one of T-43, T-44, T-32, SAIR-EQT2"
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
  if artifact_kind == "" then
    artifact_kind = "claim-state"
  end
  if not allowed_artifact_kinds[artifact_kind] then
    return nil, "artifact_kind is not supported"
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
  local slug = proposal.target:gsub("[^A-Za-z0-9_-]", "_")
  local title = proposal.title:lower():gsub("[^a-z0-9]+", "-"):gsub("^%-+", ""):gsub("%-+$", "")
  if title == "" then
    title = "proposal"
  end
  if #title > 80 then
    title = title:sub(1, 80):gsub("%-+$", "")
  end
  return "omega-open-problem/" .. slug .. "/" .. title
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
    kind = "omega-open-problem",
    ref = proposal_id,
  }
end

function M.render_consensus_context(proposal)
  return table.concat({
    "This is an Omega/Automath FKST routing proposal.",
    "Use FKST consensus only to decide whether the task should produce a durable artifact.",
    "Mathematical truth must remain in Lean, replay scripts, source ledgers, or claim-state metadata.",
    "For public-impact targets such as SAIR-EQT2, keep solver and certificate claims separate from solved-conjecture claims.",
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
    "Omega open-problem proposal.",
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
  if not bounded_string(proposal_id, 200) then
    return nil, "proposal_id is required and must be <= 200 bytes"
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
    "Approved Omega/FKST artifact task.",
    "",
    "Proposal: " .. consensus.proposal_id,
    "Dedup: " .. consensus.dedup_key,
    "",
    "Consensus body:",
    consensus.body,
    "",
    "Required output:",
    "Create or update a durable repository artifact. Do not record mathematical",
    "truth as agent consensus. If evidence is incomplete, produce a blocked or",
    "route-refutation record rather than a theorem claim.",
  }, "\n")
end

return M
