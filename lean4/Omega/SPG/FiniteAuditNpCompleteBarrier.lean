import Mathlib.Tactic
import Omega.SPG.FiniteAuditBidirectionalCertificates

namespace Omega.SPG

/-- Once SAT reduces to the finite-audit decision problem, the bidirectional certificate package
forces the usual `NP`/`coNP` collapse, and any polynomial-time solver yields the corresponding
`P = NP` consequence.
    cor:spg-finite-audit-np-complete-barrier -/
theorem paper_spg_finite_audit_np_complete_barrier {Instance Theta Mode : Type}
    (D : FiniteAuditBidirectionalCertificateData Instance Theta Mode)
    (satReducesToPi npEqCoNp pEqNp : Prop)
    (hCollapse : satReducesToPi -> D.inNP -> D.inCoNP -> npEqCoNp)
    (hP : satReducesToPi -> D.inP -> pEqNp) :
    satReducesToPi -> npEqCoNp ∧ (D.inP -> pEqNp) := by
  intro hSat
  have hNP : D.inNP := D.np_of_fullTable D.fullTableCertificate
  have hCoNP : D.inCoNP := D.conp_of_badWitness D.badWitnessCertificate
  refine ⟨hCollapse hSat hNP hCoNP, ?_⟩
  intro hInP
  exact hP hSat hInP

end Omega.SPG
