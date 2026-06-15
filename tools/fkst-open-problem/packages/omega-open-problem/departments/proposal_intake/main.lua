local core = require("core")

local M = {}

M.spec = {
  consumes = { "omega_proposal" },
  produces = { "consensus.proposal" },
}

function pipeline(event)
  local proposal, err = core.validate_proposal(event.payload or {})
  if proposal == nil then
    error("omega-open-problem: invalid proposal: " .. tostring(err))
  end
  local proposal_id = core.consensus_proposal_id(proposal)
  raise("consensus.proposal", {
    schema = core.consensus_proposal_schema(),
    proposal_id = proposal_id,
    title = proposal.title,
    body = core.render_consensus_body(proposal),
    context = core.render_consensus_context(proposal),
    angles = { "minimal", "structural", "delete" },
    verdict_mode = "gate",
    dedup_key = core.consensus_dedup_key(proposal),
    source_ref = core.consensus_source_ref(proposal, event.source_ref, proposal_id),
  })
end

return M
