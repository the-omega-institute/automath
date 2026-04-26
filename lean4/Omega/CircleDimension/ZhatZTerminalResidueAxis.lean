import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Concrete data for the residue-axis terminal object `Ẑ`: a compatible cone over the inverse
system of residue quotients, a coordinatewise mediator into the `Ẑ` model, and extensionality on
all residue coordinates. -/
structure ZhatZTerminalResidueAxisData where
  P : Type*
  ZhatModel : Type*
  residue : ℕ → Type*
  transition : ∀ {m n : ℕ}, m ≤ n → residue n → residue m
  cone : ∀ n : ℕ, P → residue n
  residueProjection : ∀ n : ℕ, ZhatModel → residue n
  mediator : P → ZhatModel
  cone_compatible :
    ∀ {m n : ℕ} (hmn : m ≤ n) (p : P), transition hmn (cone n p) = cone m p
  mediator_commutes :
    ∀ n : ℕ, ∀ p : P, residueProjection n (mediator p) = cone n p
  coordinate_extensionality :
    ∀ z z' : ZhatModel, (∀ n : ℕ, residueProjection n z = residueProjection n z') → z = z'

namespace ZhatZTerminalResidueAxisData

/-- The universal property of the terminal residue axis: any coordinatewise compatible family of
residue classes factors uniquely through the mediator into the `Ẑ` model. -/
def universal_property (D : ZhatZTerminalResidueAxisData) : Prop :=
  ∀ g : D.P → D.ZhatModel,
    (∀ n : ℕ, ∀ p : D.P, D.residueProjection n (g p) = D.cone n p) → g = D.mediator

end ZhatZTerminalResidueAxisData

/-- Paper label: `thm:cdim-zhatZ-terminal-residue-axis`.
The coordinatewise mediator into the `Ẑ` model is the unique map whose residue projections agree
with the given compatible family on every residue quotient. -/
theorem paper_cdim_zhatZ_terminal_residue_axis (D : ZhatZTerminalResidueAxisData) :
    D.universal_property := by
  intro g hg
  funext p
  apply D.coordinate_extensionality
  intro n
  rw [hg n p, D.mediator_commutes n p]

end Omega.CircleDimension
