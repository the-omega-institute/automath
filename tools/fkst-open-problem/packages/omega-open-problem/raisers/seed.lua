local M = {}

M.spec = {
  produces = { "omega_proposal" },
}

function M.pipeline()
  raise("omega_proposal", {
    target = "T-43",
    title = "Source-replay A5 same-W rank-4 certificate candidate",
    objective = table.concat({
      "Audit the A5 Godeaux-Serre same-W certificate candidate as a bounded",
      "source-replay task. Separate confirmed facts from conjectural glue:",
      "smooth projective Y/Q, finite etale A5 cover, rank-5 permutation",
      "Gauss-Manin object, rank-4 standard idempotent e = I - J/5,",
      "H^1_dR(Ytilde)=0, de Rham descent, zero p-curvature, and the exact",
      "use of E-G Theorem 1.8 + Remark 6.2.",
    }, " "),
    expected_artifact = "A claim-state JSON record plus a source-obligation ledger under tools/community-outreach or theory notes; no theorem claim unless every source replay obligation is closed.",
    source_refs = {
      "tools/community-outreach/drafts/problemsilike_02_research_summary.md",
      "tools/community-outreach/RESEARCH_BOARD.md",
    },
  })
end

return M
