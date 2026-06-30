local core = require("core")

local M = {}

M.spec = {
  consumes = { "omega_candidate_search" },
  produces = { "omega_checker_result" },
  stall_window = "20m",
}

function pipeline(event)
  local candidate_search, err = core.validate_candidate_search(event.payload or {})
  if candidate_search == nil then
    error("omega-sair-eqt2: invalid candidate search: " .. tostring(err))
  end
  local result = exec_sync({
    cmd = core.research_checker_cmd(candidate_search),
    cwd = candidate_search.repo_root,
    timeout = 900,
  })
  local checker = nil
  if result.exit_code == 0 then
    local ok, decoded = pcall(json.decode, result.stdout)
    if ok and type(decoded) == "table" then
      checker = decoded
    end
  end
  if checker == nil then
    checker = {
      target = "SAIR-EQT2",
      checker_name = "sair_eqt2_research_check.py",
      status = "checker-output-unparseable",
      exit_code = result.exit_code,
      evidence = tostring(result.stdout or ""):sub(1, 2000),
      summary = {
        text = "Checker did not return parseable JSON; no mathematical claim is made.",
      },
    }
  end
  raise("omega_checker_result", {
    target = "SAIR-EQT2",
    run_id = candidate_search.run_id,
    candidate = candidate_search.candidate,
    checker = checker,
    source_ref = candidate_search.source_ref or event.source_ref,
  })
end

return M
