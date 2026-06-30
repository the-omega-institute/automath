local core = require("core")

local M = {}

M.spec = {
  consumes = { "omega_research_task" },
  produces = { "omega_candidate_search" },
  stall_window = "2m",
}

function pipeline(event)
  local task, err = core.validate_research_task(event.payload or {})
  if task == nil then
    error("omega-sair-eqt2: invalid research task: " .. tostring(err))
  end
  for _, candidate in ipairs(core.research_portfolio_candidates(task)) do
    raise("omega_candidate_search", {
      target = "SAIR-EQT2",
      run_id = task.run_id .. "-" .. candidate.action_id,
      repo_root = task.repo_root,
      candidate = candidate,
      codex_exit_code = 0,
      codex_error_class = "",
      source_ref = event.source_ref,
    })
  end
end

return M
