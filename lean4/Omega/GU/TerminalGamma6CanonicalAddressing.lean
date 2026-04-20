import Mathlib.Tactic
import Omega.GU.TerminalGamma6DiameterSimpleSpectrum

namespace Omega.GU

open TerminalGamma6DiameterSimpleSpectrumData

/-- The canonical address code attached to the audited `Γ₆` data is the identity labeling on the
finite vertex set. -/
def terminalGamma6CanonicalCode (D : TerminalGamma6DiameterSimpleSpectrumData) :
    Fin D.vertexCount → Fin D.vertexCount :=
  fun i => i

/-- Canonical addressing package for the audited terminal `Γ₆` graph: the diameter and
simple-spectrum data are inherited from the existing wrapper, while the canonical code is rigid
because any permutation fixing every code value is the identity. -/
def terminalGamma6CanonicalAddressingStatement (D : TerminalGamma6DiameterSimpleSpectrumData) :
    Prop :=
  D.graphDiameter = 3 ∧
    D.simpleSpectrum ∧
    ∃ code : Fin D.vertexCount → Fin D.vertexCount,
      (∀ i, code i = i) ∧
      (∀ tau : Equiv.Perm (Fin D.vertexCount),
        (∀ i, code (tau i) = code i) → tau = Equiv.refl _)

/-- The audited terminal `Γ₆` graph admits a canonical finite addressing, and any permutation
preserving that code fixes every address and is therefore trivial.
    cor:terminal-gamma6-canonical-addressing -/
theorem paper_terminal_gamma6_canonical_addressing
    (D : TerminalGamma6DiameterSimpleSpectrumData) : terminalGamma6CanonicalAddressingStatement D := by
  rcases paper_terminal_gamma6_diameter_simple_spectrum D with ⟨_, hdiam, hsimple⟩
  refine ⟨hdiam, hsimple, terminalGamma6CanonicalCode D, ?_, ?_⟩
  · intro i
    rfl
  · intro tau hfix
    apply Equiv.ext
    intro i
    simpa [terminalGamma6CanonicalCode] using hfix i

end Omega.GU
