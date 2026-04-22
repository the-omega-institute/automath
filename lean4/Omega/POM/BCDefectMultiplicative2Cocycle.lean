import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.BCUniformLiftPseudofunctor

namespace Omega.POM

noncomputable section

/-- Concrete direct lift scale in the one-point Beck--Chevalley model. -/
noncomputable def pom_bc_defect_multiplicative_2cocycle_lift (n : ℕ) : ℝ :=
  1 / bcDiagonalDefect n

/-- The defect multiplier comparing sequential and direct lifts. -/
noncomputable def pom_bc_defect_multiplicative_2cocycle_rho (f g : ℕ) : ℝ :=
  bcComparisonMap f g

/-- Logarithmic form of the defect multiplier. -/
noncomputable def pom_bc_defect_multiplicative_2cocycle_log_rho (f g : ℕ) : ℝ :=
  bcLogComparisonMap f g

/-- Pointwise factorization of the sequential lift through the direct lift and the defect
multiplier. -/
theorem pom_bc_defect_multiplicative_2cocycle_factorization (f g : ℕ) :
    pom_bc_defect_multiplicative_2cocycle_lift f *
        pom_bc_defect_multiplicative_2cocycle_lift g =
      pom_bc_defect_multiplicative_2cocycle_rho f g *
        pom_bc_defect_multiplicative_2cocycle_lift (f + g) := by
  unfold pom_bc_defect_multiplicative_2cocycle_lift
    pom_bc_defect_multiplicative_2cocycle_rho bcComparisonMap bcDiagonalDefect
  field_simp

/-- Comparing the two bracketings of three consecutive lifts yields the multiplicative
`2`-cocycle law. -/
theorem pom_bc_defect_multiplicative_2cocycle_multiplicative (h f g : ℕ) :
    pom_bc_defect_multiplicative_2cocycle_rho h f *
        pom_bc_defect_multiplicative_2cocycle_rho (h + f) g =
      pom_bc_defect_multiplicative_2cocycle_rho f g *
        pom_bc_defect_multiplicative_2cocycle_rho h (f + g) := by
  simpa [pom_bc_defect_multiplicative_2cocycle_rho] using
    bcPentagonCoherence_of_diagonal_defect h f g

/-- Taking logarithms converts the multiplicative cocycle law into the normalized additive
closure relation. -/
theorem pom_bc_defect_multiplicative_2cocycle_log_closed (h f g : ℕ) :
    pom_bc_defect_multiplicative_2cocycle_log_rho h f +
        pom_bc_defect_multiplicative_2cocycle_log_rho (h + f) g =
      pom_bc_defect_multiplicative_2cocycle_log_rho f g +
        pom_bc_defect_multiplicative_2cocycle_log_rho h (f + g) := by
  simpa [pom_bc_defect_multiplicative_2cocycle_log_rho] using
    bcLogCocycleClosed_of_diagonal_defect h f g

/-- Concrete proposition encoding the pointwise factorization together with the multiplicative
and logarithmic cocycle identities. -/
def pom_bc_defect_multiplicative_2cocycle_statement : Prop :=
  (∀ f g : ℕ,
      pom_bc_defect_multiplicative_2cocycle_lift f *
          pom_bc_defect_multiplicative_2cocycle_lift g =
        pom_bc_defect_multiplicative_2cocycle_rho f g *
          pom_bc_defect_multiplicative_2cocycle_lift (f + g)) ∧
    (∀ h f g : ℕ,
      pom_bc_defect_multiplicative_2cocycle_rho h f *
          pom_bc_defect_multiplicative_2cocycle_rho (h + f) g =
        pom_bc_defect_multiplicative_2cocycle_rho f g *
          pom_bc_defect_multiplicative_2cocycle_rho h (f + g)) ∧
    ∀ h f g : ℕ,
      pom_bc_defect_multiplicative_2cocycle_log_rho h f +
          pom_bc_defect_multiplicative_2cocycle_log_rho (h + f) g =
        pom_bc_defect_multiplicative_2cocycle_log_rho f g +
          pom_bc_defect_multiplicative_2cocycle_log_rho h (f + g)

/-- Paper label wrapper for the multiplicative Beck--Chevalley defect cocycle.
    thm:pom-bc-defect-multiplicative-2cocycle -/
def paper_pom_bc_defect_multiplicative_2cocycle : Prop :=
  pom_bc_defect_multiplicative_2cocycle_statement

theorem pom_bc_defect_multiplicative_2cocycle_statement_proof :
    paper_pom_bc_defect_multiplicative_2cocycle := by
  refine ⟨?_, ?_, ?_⟩
  · intro f g
    exact pom_bc_defect_multiplicative_2cocycle_factorization f g
  · intro h f g
    exact pom_bc_defect_multiplicative_2cocycle_multiplicative h f g
  · intro h f g
    exact pom_bc_defect_multiplicative_2cocycle_log_closed h f g

end

end Omega.POM
