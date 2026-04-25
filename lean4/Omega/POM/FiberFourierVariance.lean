import Omega.OperatorAlgebra.FoldConditionalExpectation

open scoped BigOperators

namespace Omega.POM

open Omega.OperatorAlgebra
open Omega.OperatorAlgebra.FoldConditionalExpectationData

/-- Paper-facing fiber Fourier variance package: the fold average has its coordinate formula,
the centered residual has zero fiber average, and the fold average is idempotent.
    prop:pom-fiber-fourier-variance -/
theorem paper_pom_fiber_fourier_variance
    (D : Omega.OperatorAlgebra.FoldConditionalExpectationData) (fχ : D.Ω → ℚ) :
    (∀ a : D.Ω,
        D.foldExpectation fχ a =
          Finset.sum (D.fiber (D.fold a)) fχ / D.fiberCard (D.fold a)) ∧
      D.foldExpectation (fun a => fχ a - D.foldExpectation fχ a) = (fun _ => 0) ∧
        D.foldExpectation (D.foldExpectation fχ) = D.foldExpectation fχ := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rfl
  · funext a
    have hcardq : (D.fiberCard (D.fold a) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (D.fiberCard_pos (D.fold a))
    have hsumInvariant :
        Finset.sum (D.fiber (D.fold a)) (D.foldExpectation fχ) =
          (D.fiberCard (D.fold a) : ℚ) * D.foldExpectation fχ a :=
      D.sum_eq_card_mul_of_invariant
        (D.foldExpectation fχ) (D.foldExpectation_fiberInvariant fχ) a
    calc
      D.foldExpectation (fun a => fχ a - D.foldExpectation fχ a) a =
          (Finset.sum (D.fiber (D.fold a)) fχ -
              Finset.sum (D.fiber (D.fold a)) (D.foldExpectation fχ)) /
            D.fiberCard (D.fold a) := by
            rw [FoldConditionalExpectationData.foldExpectation, Finset.sum_sub_distrib]
      _ = (Finset.sum (D.fiber (D.fold a)) fχ -
              (D.fiberCard (D.fold a) : ℚ) * D.foldExpectation fχ a) /
            D.fiberCard (D.fold a) := by
            rw [hsumInvariant]
      _ = 0 := by
            rw [FoldConditionalExpectationData.foldExpectation]
            field_simp [hcardq]
            ring
  · exact D.foldExpectation_idempotent fχ

end Omega.POM
