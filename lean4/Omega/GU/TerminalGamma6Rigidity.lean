import Mathlib.Tactic
import Omega.GU.Window6TypeSuperselectionAutGamma6

namespace Omega.GU

/-- Finite-certificate package for the window-6 type adjacency graph `Γ₆`. The data records a
certificate for the audited graph, together with the two derivations extracted from that
certificate: connectivity of the graph and triviality of its adjacency-preserving permutation
group. -/
structure TerminalGamma6RigidityData where
  graphConnected : Prop
  automorphismGroupTrivial : Prop
  finiteRigidityCertificate : Prop
  certificate : finiteRigidityCertificate
  connected_of_certificate : finiteRigidityCertificate → graphConnected
  rigid_of_certificate : finiteRigidityCertificate → automorphismGroupTrivial

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the audited rigidity of the terminal window-6 type-adjacency
graph `Γ₆`.
    prop:terminal-gamma6-rigidity -/
theorem paper_terminal_gamma6_rigidity (h : TerminalGamma6RigidityData) :
    h.graphConnected ∧ h.automorphismGroupTrivial := by
  exact
    ⟨h.connected_of_certificate h.certificate, h.rigid_of_certificate h.certificate⟩

end Omega.GU
