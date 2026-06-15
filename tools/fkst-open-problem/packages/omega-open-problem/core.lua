local M = {}

local allowed_targets = {
  ["T-43"] = true,
  ["T-44"] = true,
  ["T-32"] = true,
}

local max_text = 6000

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
    return nil, "target must be one of T-43, T-44, T-32"
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
  return {
    target = target,
    title = title,
    objective = objective,
    expected_artifact = expected,
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
    "Source references:",
    table.concat(refs, "\n"),
    "",
    "Acceptance rule:",
    "Approve only if the proposal can produce a durable repository artifact. Consensus is not a proof.",
  }, "\n")
end

return M
