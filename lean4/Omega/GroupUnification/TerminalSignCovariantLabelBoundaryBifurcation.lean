import Omega.GroupUnification.BdryOrientationParityUplift
import Omega.GroupUnification.BdryThreeLayerSymmetricBinaryLiftWreathQuotient

namespace Omega.GroupUnification

/-- Recorded boundary-fiber cardinalities for the audited `m = 6, 7, 8` cases. -/
def terminalBoundaryFiberCardinality : Nat → Nat
  | 6 => 2
  | 7 => 3
  | 8 => 3
  | _ => 0

/-- The sign-twisted binary label exists exactly when the binary orientation object matches the
literal layer-label cardinality. -/
def signTwistedLabelExists (d : Nat) : Prop :=
  boundaryOrientationCardinality d = boundarySheetParityCardinality d

theorem signTwistedLabelExists_iff (d : Nat) : signTwistedLabelExists d ↔ d = 2 := by
  unfold signTwistedLabelExists boundaryOrientationCardinality boundarySheetParityCardinality
  constructor
  · intro h
    simpa using h.symm
  · intro h
    simpa [h]

private theorem two_layer_realizable : signTwistedLabelExists 2 := by
  simpa [signTwistedLabelExists] using (paper_bdry_orientation_parity_uplift).2.1

private theorem three_layer_nonrealizable : ¬ signTwistedLabelExists 3 := by
  simpa [signTwistedLabelExists] using (paper_bdry_orientation_parity_uplift).2.2.2

/-- Concrete package for the terminal sign-covariant label bifurcation statement. The only free
input is the tested boundary-fiber cardinality; the `m = 6, 7, 8` fibers are the recorded
boundary cases. -/
structure TerminalSignCovariantLabelBoundaryBifurcationData where
  cardinality : Nat

namespace TerminalSignCovariantLabelBoundaryBifurcationData

def signCovariantExists (D : TerminalSignCovariantLabelBoundaryBifurcationData) : Prop :=
  signTwistedLabelExists D.cardinality

def m6Realizable (_D : TerminalSignCovariantLabelBoundaryBifurcationData) : Prop :=
  signTwistedLabelExists (terminalBoundaryFiberCardinality 6)

def m7Realizable (_D : TerminalSignCovariantLabelBoundaryBifurcationData) : Prop :=
  signTwistedLabelExists (terminalBoundaryFiberCardinality 7)

def m8Realizable (_D : TerminalSignCovariantLabelBoundaryBifurcationData) : Prop :=
  signTwistedLabelExists (terminalBoundaryFiberCardinality 8)

end TerminalSignCovariantLabelBoundaryBifurcationData

/-- Paper package for the sign-covariant boundary-label bifurcation. The main equivalence is the
`d = 2` sign-twisted-label criterion; the `m = 6, 7, 8` cases are the recorded two-layer versus
three-layer boundary fibers. `prop:terminal-sign-covariant-label-boundary-bifurcation` -/
theorem paper_terminal_sign_covariant_label_boundary_bifurcation
    (D : TerminalSignCovariantLabelBoundaryBifurcationData) :
    (D.signCovariantExists ↔ D.cardinality = 2) ∧ D.m6Realizable ∧ ¬ D.m7Realizable ∧
      ¬ D.m8Realizable := by
  let _ := paper_bdry_three_layer_symmetric_binary_lift_wreath_quotient
  refine ⟨signTwistedLabelExists_iff D.cardinality, ?_, ?_, ?_⟩
  · simpa [TerminalSignCovariantLabelBoundaryBifurcationData.m6Realizable,
      terminalBoundaryFiberCardinality] using two_layer_realizable
  · simpa [TerminalSignCovariantLabelBoundaryBifurcationData.m7Realizable,
      terminalBoundaryFiberCardinality] using three_layer_nonrealizable
  · simpa [TerminalSignCovariantLabelBoundaryBifurcationData.m8Realizable,
      terminalBoundaryFiberCardinality] using three_layer_nonrealizable

end Omega.GroupUnification
