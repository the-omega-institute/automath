import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- The concrete diagonal normalization attached to an `n`-fold uniform lift. -/
def bcDiagonalDefect (n : ℕ) : ℝ :=
  n + 1

/-- The comparison `2`-morphism between the sequential and direct uniform lifts. -/
def bcComparisonMap (f g : ℕ) : ℝ :=
  bcDiagonalDefect (f + g) / (bcDiagonalDefect f * bcDiagonalDefect g)

/-- The additive logarithmic defect whose coboundary controls the pentagon. -/
def bcLogComparisonMap (f g : ℕ) : ℝ :=
  Real.log (bcDiagonalDefect (f + g)) - Real.log (bcDiagonalDefect f) -
    Real.log (bcDiagonalDefect g)

/-- The multiplicative pentagon identity for the comparison maps `α_{f,g}`. -/
def bcPentagonCoherence (h f g : ℕ) : Prop :=
  bcComparisonMap h f * bcComparisonMap (h + f) g =
    bcComparisonMap f g * bcComparisonMap h (f + g)

/-- The vanishing of the additive coboundary `δ(log ρ)`. -/
def bcLogCocycleClosed (h f g : ℕ) : Prop :=
  bcLogComparisonMap h f + bcLogComparisonMap (h + f) g =
    bcLogComparisonMap f g + bcLogComparisonMap h (f + g)

lemma bcPentagonCoherence_of_diagonal_defect (h f g : ℕ) :
    bcPentagonCoherence h f g := by
  unfold bcPentagonCoherence bcComparisonMap bcDiagonalDefect
  field_simp
  ring

lemma bcLogCocycleClosed_of_diagonal_defect (h f g : ℕ) :
    bcLogCocycleClosed h f g := by
  unfold bcLogCocycleClosed bcLogComparisonMap
  ring_nf

/-- A concrete pseudofunctor-strictification model for the Beck--Chevalley uniform lifts:
the multiplicative comparison maps satisfy the pentagon, and after taking logarithms the same
statement becomes the cocycle identity `δ(log ρ)=0`.
    thm:pom-bc-uniform-lift-pseudofunctor -/
theorem paper_pom_bc_uniform_lift_pseudofunctor (h f g : ℕ) :
    bcPentagonCoherence h f g ∧ bcLogCocycleClosed h f g := by
  exact ⟨bcPentagonCoherence_of_diagonal_defect h f g,
    bcLogCocycleClosed_of_diagonal_defect h f g⟩

end

end Omega.POM
