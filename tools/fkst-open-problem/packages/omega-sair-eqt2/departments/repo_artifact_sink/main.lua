local M = {}

M.spec = {
  consumes = { "omega_repo_artifact" },
  produces = {},
  stall_window = "2m",
}

local function one_line(value)
  return tostring(value or ""):gsub("%s+", " ")
end

function pipeline(event)
  local payload = event.payload or {}
  if payload.schema ~= "omega.repo_artifact.v1" then
    return
  end
  log.warn(
    "omega-sair-eqt2 dept=repo_artifact_sink tag=DRY_RUN_REPO_ARTIFACT"
      .. " path=" .. one_line(payload.path)
      .. " proposal_id=" .. one_line(payload.proposal_id)
      .. " dedup_key=" .. one_line(payload.dedup_key)
      .. " content_bytes=" .. tostring(#tostring(payload.content or ""))
      .. " github_write=false"
  )
end

return M
