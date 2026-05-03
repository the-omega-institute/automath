import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-node-polynomial-rational-reconstruction`. -/
theorem paper_xi_node_polynomial_rational_reconstruction
    (finiteWindow h0Invertible nodePolynomialOverRationalField rootsAreNodeSpectrum
      symmetricInvariantsRecoverable : Prop)
    (hpoly : finiteWindow → h0Invertible → nodePolynomialOverRationalField)
    (hroots : nodePolynomialOverRationalField → rootsAreNodeSpectrum)
    (hsymm : rootsAreNodeSpectrum → symmetricInvariantsRecoverable)
    (hwin : finiteWindow) (hinv : h0Invertible) :
    nodePolynomialOverRationalField ∧ rootsAreNodeSpectrum ∧
      symmetricInvariantsRecoverable := by
  have hnode : nodePolynomialOverRationalField := hpoly hwin hinv
  have hspectrum : rootsAreNodeSpectrum := hroots hnode
  exact ⟨hnode, hspectrum, hsymm hspectrum⟩

end Omega.Zeta
