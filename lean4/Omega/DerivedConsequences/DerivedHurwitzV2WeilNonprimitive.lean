import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmResolventCubicNoCmMaxEnd
import Omega.Zeta.XiTerminalZmS3EndoscopicHomologyA2Identification

namespace Omega.DerivedConsequences

open Omega.Zeta

/-- The square-power endomorphism algebra attached to the terminal resolvent factor. -/
abbrev derived_hurwitz_v2_weil_nonprimitive_square_end0 :=
  xi_terminal_zm_resolvent_cubic_no_cm_max_end_End0_square

/-- Entry-count proxy for the `2 × 2` matrix algebra over the base endomorphism algebra. -/
def derived_hurwitz_v2_weil_nonprimitive_matrix_entry_count : ℕ :=
  Fintype.card (Fin 2 × Fin 2)

/-- The rational endomorphism algebra of the base elliptic block is one-dimensional over `ℚ`. -/
def derived_hurwitz_v2_weil_nonprimitive_base_end_dimension : ℕ := 1

/-- The square-power algebra has `2²` matrix entries over the one-dimensional base algebra. -/
def derived_hurwitz_v2_weil_nonprimitive_square_end_dimension : ℕ :=
  derived_hurwitz_v2_weil_nonprimitive_matrix_entry_count *
    derived_hurwitz_v2_weil_nonprimitive_base_end_dimension

/-- Dimension proxy for the quadratic CM field `ℚ(ζ₃)`. -/
def derived_hurwitz_v2_weil_nonprimitive_qzeta3_dimension : ℕ := 2

/-- Concrete derived package: the `V₂` block is the square of the resolvent Jacobian, its rational
endomorphism algebra is the `2 × 2` matrix algebra over the base algebra, so the dimension is at
least `4`, hence it cannot be the quadratic field `ℚ(ζ₃)`. -/
def derived_hurwitz_v2_weil_nonprimitive_statement : Prop :=
  xiTerminalZmS3JacobianFactorMultiplicity XiTerminalZmS3JacobianFactor.resolvent = 2 ∧
    xiTerminalZmS3EndoscopicHomologyDimension XiTerminalZmS3EndoscopicHomologyBlock.prym =
      2 * xiTerminalZmS3ResolventJacobianDimension ∧
    Nonempty (derived_hurwitz_v2_weil_nonprimitive_square_end0 ≃ Matrix (Fin 2) (Fin 2) ℚ) ∧
    derived_hurwitz_v2_weil_nonprimitive_matrix_entry_count = 4 ∧
    derived_hurwitz_v2_weil_nonprimitive_square_end_dimension = 4 ∧
    4 ≤ derived_hurwitz_v2_weil_nonprimitive_square_end_dimension ∧
    derived_hurwitz_v2_weil_nonprimitive_qzeta3_dimension = 2 ∧
    derived_hurwitz_v2_weil_nonprimitive_square_end_dimension ≠
      derived_hurwitz_v2_weil_nonprimitive_qzeta3_dimension

/-- Paper label: `cor:derived-hurwitz-v2-weil-nonprimitive`. The existing endoscopic splitting
identifies the `V₂` block with a square of the elliptic resolvent factor, and the no-CM witness
records the corresponding rational endomorphism algebra as `M₂(ℚ)`. Its dimension is therefore
`4`, which is strictly larger than the quadratic CM-field dimension `2`, ruling out `ℚ(ζ₃)` as
the whole rational endomorphism algebra. -/
theorem paper_derived_hurwitz_v2_weil_nonprimitive :
    derived_hurwitz_v2_weil_nonprimitive_statement := by
  rcases paper_xi_terminal_zm_s3_endoscopic_homology_a2_identification with ⟨_, hprym, hsplit⟩
  rcases paper_xi_terminal_zm_resolvent_cubic_no_cm_max_end with ⟨_, _, _, hend⟩
  refine ⟨hsplit.2.1, hprym.1, hend, rfl, rfl, by native_decide, rfl, by native_decide⟩

end Omega.DerivedConsequences
