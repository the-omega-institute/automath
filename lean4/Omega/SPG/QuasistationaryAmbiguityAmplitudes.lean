namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the quasistationary ambiguity amplitudes theorem in the
    scan-projection ETDS paper.
    thm:quasistationary-ambiguity -/
theorem paper_scan_projection_address_quasistationary_ambiguity_amplitudes
    {Residue : Type}
    (leftEigenvector : Prop)
    (ratioLimit xiWeight asymptoticWeight : Residue → ℝ)
    (hEigen : leftEigenvector)
    (hRatio : ∀ r : Residue, ratioLimit r = xiWeight r)
    (hAsymptotic : ∀ r : Residue, asymptoticWeight r = ratioLimit r) :
    leftEigenvector ∧
      (∀ r : Residue, ratioLimit r = xiWeight r) ∧
      (∀ r : Residue, asymptoticWeight r = xiWeight r) := by
  refine ⟨hEigen, hRatio, ?_⟩
  intro r
  rw [hAsymptotic r, hRatio r]

end Omega.SPG
