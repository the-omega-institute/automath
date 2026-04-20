import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The exact target signature from the paper-facing wrapper request is not derivable in Lean
without extra hypotheses connecting `sturmCertified` to the zero set of some polynomial. This
counterexample shows the quantified statement is false for arbitrary predicates.
    thm:pom-newman-critical-algebraic-elimination-sturm -/
theorem paper_pom_newman_critical_algebraic_elimination_sturm_signature_unprovable :
    ¬
      (∀ (criticalPoint algebraicCertified sturmCertified : Real -> Prop)
        (vanishesAt : Polynomial Int -> Real -> Prop),
        ∃ Pdelta : Polynomial Int,
          Pdelta ≠ 0 ∧
            (∀ t : Real, criticalPoint t -> vanishesAt Pdelta t) ∧
            (∀ t : Real, vanishesAt Pdelta t -> algebraicCertified t) ∧
            (∀ t : Real, sturmCertified t ↔ vanishesAt Pdelta t)) := by
  intro h
  let criticalPoint : Real -> Prop := fun _ => False
  let algebraicCertified : Real -> Prop := fun _ => True
  let sturmCertified : Real -> Prop := fun t => t = 0
  let vanishesAt : Polynomial Int -> Real -> Prop := fun _ _ => False
  rcases h criticalPoint algebraicCertified sturmCertified vanishesAt with
    ⟨Pdelta, _, _, _, hSturm⟩
  have hZero : sturmCertified 0 ↔ vanishesAt Pdelta 0 := hSturm 0
  simp [sturmCertified, vanishesAt] at hZero

end Omega.POM
