import Mathlib.Tactic
import Omega.Conclusion.SemanticEquivalenceUndecidable
import Omega.Folding.HaltingNoComputableModulusSparseMoments

namespace Omega.FoldComputability

open Omega.Conclusion

noncomputable section

/-- The atomic-mass query family read from the one-atom Lee--Yang encoding attached to the
halting index `e`. -/
def fold_computability_halting_no_computable_modulus_atomic_query_family
    (halts : ℕ → Prop) (e : ℕ) : ℚ :=
  Omega.Folding.fold_computability_halting_no_computable_modulus_sparse_moments_target halts e

/-- The dyadic precision threshold `k(e)` used to separate the zero and halting cases. -/
def fold_computability_halting_no_computable_modulus_precision_threshold (e : ℕ) : ℚ :=
  (((2 : ℚ) ^ e)⁻¹) / 6

/-- The atomic-mass approximation obtained by simulating the machine indexed by `e` for `M e`
steps and returning either the queried atom or `0`. -/
def fold_computability_halting_no_computable_modulus_atomic_query_approximation
    (haltsWithin : ℕ → ℕ → Prop) (halts : ℕ → Prop) (M : ℕ → ℕ) (e : ℕ) : ℚ :=
  by
    classical
    exact
      if haltsWithin e (M e) then
        fold_computability_halting_no_computable_modulus_atomic_query_family halts e
      else
        0

/-- Paper-facing no-computable-modulus statement: a uniform total modulus for the atomic-mass
queries would decide halting by a single finite-step simulation at stage `M e`. -/
def fold_computability_halting_no_computable_modulus_statement : Prop :=
  ∀ (haltsWithin : ℕ → ℕ → Prop) (halts : ℕ → Prop),
    RelationPointwiseDecidable haltsWithin →
    (∀ e, halts e ↔ ∃ N, haltsWithin e N) →
    ¬ PredicatePointwiseDecidable halts →
    ¬ ∃ M : ℕ → ℕ,
      ∀ e,
        let target :=
          fold_computability_halting_no_computable_modulus_atomic_query_family halts e
        let approx :=
          fold_computability_halting_no_computable_modulus_atomic_query_approximation
            haltsWithin halts M e
        |approx - target| <
          fold_computability_halting_no_computable_modulus_precision_threshold e

/-- Paper label: `cor:fold-computability-halting-no-computable-modulus`. -/
theorem paper_fold_computability_halting_no_computable_modulus :
    fold_computability_halting_no_computable_modulus_statement := by
  intro haltsWithin halts hStepDec hHalts hUndecidable hM
  rcases hStepDec with ⟨hStepDecidable⟩
  rcases hM with ⟨M, hM⟩
  apply hUndecidable
  refine ⟨fun e => ?_⟩
  letI := hStepDecidable e (M e)
  by_cases hstep : haltsWithin e (M e)
  · exact isTrue ((hHalts e).2 ⟨M e, hstep⟩)
  · refine isFalse ?_
    intro hh
    have hbound := hM e
    have htarget :
        fold_computability_halting_no_computable_modulus_atomic_query_family halts e =
          (((2 : ℚ) ^ e)⁻¹) := by
      simpa [fold_computability_halting_no_computable_modulus_atomic_query_family,
        Omega.Folding.fold_computability_halting_no_computable_modulus_sparse_moments_dyadic_weight, hh] using
        Omega.Folding.fold_computability_halting_no_computable_modulus_sparse_moments_target_eq halts e
    have hsmall :
        |(0 : ℚ) -
            fold_computability_halting_no_computable_modulus_atomic_query_family halts e| <
          (((2 : ℚ) ^ e)⁻¹) / 6 := by
      simpa [fold_computability_halting_no_computable_modulus_atomic_query_family,
        fold_computability_halting_no_computable_modulus_atomic_query_approximation,
        fold_computability_halting_no_computable_modulus_precision_threshold, hstep] using hbound
    have :
        |(0 : ℚ) - (((2 : ℚ) ^ e)⁻¹)| < (((2 : ℚ) ^ e)⁻¹) / 6 := by
      simpa [htarget] using hsmall
    have habs : (((2 : ℚ) ^ e)⁻¹) < (((2 : ℚ) ^ e)⁻¹) / 6 := by
      simpa using this
    exact Omega.Folding.fold_computability_halting_no_computable_modulus_sparse_moments_not_small e habs

end

end Omega.FoldComputability
