local core = require("core")

local M = {}

M.spec = {
  consumes = { "omega_proposal" },
  produces = { "consensus.proposal" },
}

function M.pipeline(event)
  local proposal, err = core.validate_proposal(event.payload or {})
  if proposal == nil then
    error("omega-open-problem: invalid proposal: " .. tostring(err))
  end
  raise("consensus.proposal", {
    proposal_id = core.consensus_proposal_id(proposal),
    title = proposal.title,
    body = core.render_consensus_body(proposal),
    angles = { "minimal", "structural", "delete" },
    verdict_mode = "gate",
    source_ref = event.source_ref,
  })
end

return M
