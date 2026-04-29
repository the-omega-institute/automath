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

/-- Concrete eliminant-certificate package for the paper's algebraic elimination statement.
The witness polynomial is explicit, and vanishing is interpreted as real evaluation to zero. -/
structure NewmanCriticalAlgebraicEliminationSturmData where
  criticalPoint : Real → Prop
  algebraicCertified : Real → Prop
  sturmCertified : Real → Prop
  eliminant : Polynomial Int
  eliminant_ne_zero : eliminant ≠ 0
  critical_to_eliminant_zero :
    ∀ t : Real, criticalPoint t → Polynomial.eval₂ (Int.castRingHom Real) t eliminant = 0
  eliminant_zero_to_algebraic :
    ∀ t : Real, Polynomial.eval₂ (Int.castRingHom Real) t eliminant = 0 → algebraicCertified t
  sturm_iff_eliminant_zero :
    ∀ t : Real, sturmCertified t ↔ Polynomial.eval₂ (Int.castRingHom Real) t eliminant = 0

namespace NewmanCriticalAlgebraicEliminationSturmData

/-- A real number is a vanishing point of `P` when the integer polynomial evaluates to zero after
the canonical coercion into `ℝ`. -/
def vanishesAt (_D : NewmanCriticalAlgebraicEliminationSturmData) (P : Polynomial Int)
    (t : Real) : Prop :=
  Polynomial.eval₂ (Int.castRingHom Real) t P = 0

end NewmanCriticalAlgebraicEliminationSturmData

open NewmanCriticalAlgebraicEliminationSturmData

/-- Paper label: `thm:pom-newman-critical-algebraic-elimination-sturm`. -/
theorem paper_pom_newman_critical_algebraic_elimination_sturm
    (D : NewmanCriticalAlgebraicEliminationSturmData) :
    ∃ Pdelta : Polynomial Int,
      Pdelta ≠ 0 ∧
        (∀ t : Real, D.criticalPoint t → D.vanishesAt Pdelta t) ∧
        (∀ t : Real, D.vanishesAt Pdelta t → D.algebraicCertified t) ∧
        (∀ t : Real, D.sturmCertified t ↔ D.vanishesAt Pdelta t) := by
  refine ⟨D.eliminant, D.eliminant_ne_zero, ?_, ?_, ?_⟩
  · intro t ht
    simpa [NewmanCriticalAlgebraicEliminationSturmData.vanishesAt] using
      D.critical_to_eliminant_zero t ht
  · intro t ht
    exact D.eliminant_zero_to_algebraic t <| by
      simpa [NewmanCriticalAlgebraicEliminationSturmData.vanishesAt] using ht
  · intro t
    simpa [NewmanCriticalAlgebraicEliminationSturmData.vanishesAt] using
      D.sturm_iff_eliminant_zero t

end Omega.POM
