local core = require("core")

local M = {}

M.spec = {
  consumes = { "consensus.consensus_reached" },
  produces = { "omega_artifact_task" },
}

function pipeline(event)
  local consensus, err = core.validate_consensus_reached(event.payload or {})
  if consensus == nil then
    return
  end
  raise("omega_artifact_task", {
    schema = "omega.artifact_task.v1",
    proposal_id = consensus.proposal_id,
    dedup_key = consensus.dedup_key,
    body = core.render_artifact_task(consensus),
    source_ref = consensus.source_ref or event.source_ref,
  })
end

return M
