local core = require("core")

local M = {}

M.spec = {
  consumes = { "omega_artifact_task" },
  produces = { "omega_repo_artifact" },
  stall_window = "2m",
}

function pipeline(event)
  local task, err = core.validate_artifact_task(event.payload or {})
  if task == nil then
    error("omega-open-problem: invalid artifact task: " .. tostring(err))
  end
  raise("omega_repo_artifact", core.render_repo_artifact(task))
end

return M
