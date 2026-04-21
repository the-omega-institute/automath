import Mathlib.Tactic
import Omega.POM.KappaKlDecomposition
import Omega.POM.MaxentLift

namespace Omega.POM

open scoped BigOperators

section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `κ(π)` is the excess entropy of the explicit fiber-uniform lift over the base entropy. -/
theorem paper_pom_kappa_derivable {X : Type*} [Fintype X] [DecidableEq X] (d : X → Nat)
    (hd : ∀ x, 0 < d x) (pi : X → Real) :
    Omega.POM.kappa d pi =
      Omega.POM.liftEntropy d (Omega.POM.fiberUniformLift d pi) -
        Finset.univ.sum (fun x : X => Real.negMulLog (pi x)) := by
  have hUniform : FiberwiseUniform d (fiberUniformLift d pi) := by
    intro x i j
    rfl
  have hMarginal : ∀ x, fiberMarginal d (fiberUniformLift d pi) x = pi x := by
    intro x
    have hd0 : (d x : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (hd x)
    calc
      fiberMarginal d (fiberUniformLift d pi) x = ∑ _i : Fin (d x), pi x / d x := by
        simp [fiberMarginal, fiberUniformLift]
      _ = (d x : ℝ) * (pi x / d x) := by
        simp
      _ = pi x := by
        field_simp [hd0]
  have hLiftEntropy :
      liftEntropy d (fiberUniformLift d pi) =
        (∑ x : X, Real.negMulLog (pi x)) + ∑ x : X, pi x * Real.log (d x) :=
    (paper_pom_maxent_lift d hd pi (fiberUniformLift d pi) hUniform hMarginal).2
  calc
    kappa d pi = ∑ x : X, pi x * Real.log (d x) := rfl
    _ = liftEntropy d (fiberUniformLift d pi) - ∑ x : X, Real.negMulLog (pi x) := by
      linarith

end

end Omega.POM
