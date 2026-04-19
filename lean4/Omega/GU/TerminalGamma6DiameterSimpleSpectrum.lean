import Mathlib.Tactic
import Omega.GU.TerminalGamma6Rigidity

namespace Omega.GU

/-- Finite certified data for the terminal `Γ₆` graph, extending the existing rigidity package
with a concrete diameter value and a simple-spectrum certificate phrased as equality between the
number of distinct eigenvalues and the number of vertices. -/
structure TerminalGamma6DiameterSimpleSpectrumData where
  rigidity : TerminalGamma6RigidityData
  graphDiameter : ℕ
  distinctEigenvalueCount : ℕ
  vertexCount : ℕ
  diameterCertificate : graphDiameter = 3
  simpleSpectrumCertificate : distinctEigenvalueCount = vertexCount

namespace TerminalGamma6DiameterSimpleSpectrumData

/-- The connectivity clause is inherited from the audited `Γ₆` rigidity package. -/
def graphConnected (D : TerminalGamma6DiameterSimpleSpectrumData) : Prop :=
  D.rigidity.graphConnected

/-- The spectrum is simple exactly when the graph has as many distinct eigenvalues as vertices. -/
def simpleSpectrum (D : TerminalGamma6DiameterSimpleSpectrumData) : Prop :=
  D.distinctEigenvalueCount = D.vertexCount

end TerminalGamma6DiameterSimpleSpectrumData

open TerminalGamma6DiameterSimpleSpectrumData

/-- Certificate-unpacking wrapper for the audited `Γ₆` graph: the inherited rigidity package gives
connectivity, the extra metadata certifies diameter `3`, and the eigenvalue count certifies simple
spectrum.
    cor:terminal-gamma6-diameter-simple-spectrum -/
theorem paper_terminal_gamma6_diameter_simple_spectrum
    (D : TerminalGamma6DiameterSimpleSpectrumData) :
    D.graphConnected ∧ D.graphDiameter = 3 ∧ D.simpleSpectrum := by
  have hRigidity : D.graphConnected ∧ D.rigidity.automorphismGroupTrivial :=
    paper_terminal_gamma6_rigidity D.rigidity
  refine ⟨hRigidity.1, D.diameterCertificate, ?_⟩
  exact D.simpleSpectrumCertificate

end Omega.GU
