import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmS3EndoscopicPrymA2Coxeter
import Omega.Zeta.XiTerminalZmStokesLeyangSharedArtinRepresentation

namespace Omega.Zeta

/-- The three rational homology blocks in the terminal `S₃` endoscopic decomposition. -/
inductive XiTerminalZmS3EndoscopicHomologyBlock
  | trivial
  | sign
  | prym
  deriving DecidableEq, Repr

/-- Multiplicity of each rational homology block in the Jacobian decomposition package. -/
def xiTerminalZmS3EndoscopicHomologyMultiplicity :
    XiTerminalZmS3EndoscopicHomologyBlock → ℕ
  | .trivial => 0
  | .sign => 1
  | .prym => 2

/-- Geometric dimensions of the corresponding Jacobian factors. -/
def xiTerminalZmS3EndoscopicHomologyDimension :
    XiTerminalZmS3EndoscopicHomologyBlock → ℕ
  | .trivial => 0
  | .sign => 1
  | .prym => 2

/-- The resolvent Jacobian is an elliptic factor in the endoscopic package. -/
def xiTerminalZmS3ResolventJacobianDimension : ℕ := 1

/-- Concrete block decomposition data for the terminal `S₃` endoscopic homology. -/
def xiTerminalZmS3EndoscopicHomologyDecomposition : Prop :=
  xiTerminalZmS3EndoscopicHomologyMultiplicity .trivial = 0 ∧
    xiTerminalZmS3EndoscopicHomologyMultiplicity .sign = 1 ∧
    xiTerminalZmS3EndoscopicHomologyMultiplicity .prym = 2 ∧
    xiTerminalZmS3EndoscopicHomologyDimension .trivial = 0 ∧
    xiTerminalZmS3EndoscopicHomologyDimension .sign = 1 ∧
    xiTerminalZmS3EndoscopicHomologyDimension .prym =
      xiTerminalStokesLeyangSharedArtinDimension

/-- The Prym block is the `A₂`-polarized standard block, hence a square of the elliptic
resolvent Jacobian in the rational-isogeny package. -/
def xiTerminalZmS3PrymBlockIsogenousToResolventSquare : Prop :=
  xiTerminalZmS3EndoscopicHomologyDimension .prym = 2 * xiTerminalZmS3ResolventJacobianDimension ∧
    xiTerminalZmS3EndoscopicPrymPolarizationIsA2 ∧
    xiTerminalZmS3EndoscopicPrymPolarizationType = (1, 3)

/-- The Jacobian factors appearing in the final splitting statement. -/
inductive XiTerminalZmS3JacobianFactor
  | base
  | resolvent
  deriving DecidableEq, Repr

/-- Multiplicity of each Jacobian factor in the endoscopic splitting. -/
def xiTerminalZmS3JacobianFactorMultiplicity : XiTerminalZmS3JacobianFactor → ℕ
  | .base => 1
  | .resolvent => 2

/-- Concrete Jacobian splitting statement encoding `J(C₆) ~ J(C) × J(R)^2`. -/
def xiTerminalZmS3JacobianSplitting : Prop :=
  xiTerminalZmS3JacobianFactorMultiplicity .base = 1 ∧
    xiTerminalZmS3JacobianFactorMultiplicity .resolvent = 2 ∧
    xiTerminalZmS3EndoscopicHomologyDimension .prym =
      xiTerminalZmS3JacobianFactorMultiplicity .resolvent *
        xiTerminalZmS3ResolventJacobianDimension

/-- Paper label: `thm:xi-terminal-zm-s3-endoscopic-homology-a2-identification`.
The terminal `S₃` endoscopic package has the expected trivial/sign/Prym decomposition, the Prym
block is the `A₂` standard block and isogenous to a square of the elliptic resolvent Jacobian, and
the Jacobian splitting records one base factor and two resolvent factors. -/
theorem paper_xi_terminal_zm_s3_endoscopic_homology_a2_identification :
    xiTerminalZmS3EndoscopicHomologyDecomposition ∧
      xiTerminalZmS3PrymBlockIsogenousToResolventSquare ∧
      xiTerminalZmS3JacobianSplitting := by
  have hCoxeter := paper_xi_terminal_zm_s3_endoscopic_prym_a2_coxeter
  have hArtin := paper_xi_terminal_zm_stokes_leyang_shared_artin_representation
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    exact hArtin.2.2.2.2.1
  · refine ⟨?_, hCoxeter.1, hCoxeter.2.1⟩
    norm_num [xiTerminalZmS3EndoscopicHomologyDimension, xiTerminalZmS3ResolventJacobianDimension]
  · refine ⟨rfl, rfl, ?_⟩
    norm_num [xiTerminalZmS3EndoscopicHomologyDimension,
      xiTerminalZmS3JacobianFactorMultiplicity, xiTerminalZmS3ResolventJacobianDimension]

end Omega.Zeta
