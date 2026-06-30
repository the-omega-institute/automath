local core = require("core")

local M = {}

M.spec = {
  consumes = { "omega_checker_result" },
  produces = { "omega_repo_artifact" },
  stall_window = "2m",
}

function pipeline(event)
  local result, err = core.validate_checker_result(event.payload or {})
  if result == nil then
    error("omega-sair-eqt2: invalid checker result: " .. tostring(err))
  end
  raise("omega_repo_artifact", core.render_research_artifact(result))
end

return M
