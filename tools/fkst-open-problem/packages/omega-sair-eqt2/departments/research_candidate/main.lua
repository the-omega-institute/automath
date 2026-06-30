local core = require("core")

local M = {}

M.spec = {
  consumes = { "omega_codex_research_task" },
  produces = { "omega_candidate_search" },
  stall_window = "20m",
}

function pipeline(event)
  local task, err = core.validate_research_task(event.payload or {})
  if task == nil then
    error("omega-sair-eqt2: invalid research task: " .. tostring(err))
  end
  local enabled = exec_sync({ cmd = core.codex_advisory_enabled_cmd(), timeout = 30 })
  if enabled.exit_code ~= 0 or tostring(enabled.stdout or "") ~= "1" then
    log.warn(
      "omega-sair-eqt2 dept=research_candidate tag=CODEX_ADVISORY_DISABLED"
        .. " run_id=" .. tostring(task.run_id)
    )
    return
  end
  local prompt = core.render_research_candidate_prompt(task)
  local result = spawn_codex_sync(core.research_codex_opts(prompt, task.repo_root))
  local candidate = core.parse_research_candidate(result.stdout)
  if result.exit_code ~= 0 then
    candidate.state = "codex-failed"
    candidate.parse_error = tostring(result.error_class or result.stderr or "codex failed")
  end
  raise("omega_candidate_search", {
    target = "SAIR-EQT2",
    run_id = task.run_id,
    repo_root = task.repo_root,
    candidate = candidate,
    codex_exit_code = result.exit_code,
    codex_error_class = result.error_class,
    source_ref = event.source_ref,
  })
end

return M
