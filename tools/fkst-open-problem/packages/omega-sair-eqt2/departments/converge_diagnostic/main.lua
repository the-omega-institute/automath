local core = require("core")

local M = {}

M.spec = {
  consumes = { "consensus.consensus_converge" },
  produces = { "omega_artifact_task" },
  stall_window = "2m",
}

function pipeline(event)
  local converge, err = core.validate_consensus_converge(event.payload or {})
  if converge == nil then
    return
  end
  raise("omega_artifact_task", core.render_converge_artifact_task(converge))
end

return M
