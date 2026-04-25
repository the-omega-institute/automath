import Mathlib.Tactic
import Omega.Conclusion.SemanticEquivalenceUndecidable
import Omega.Folding.HaltingLeyangHolographicEncoding

namespace Omega.Folding

open Omega.Conclusion
open HaltingLeyangEncodingData

noncomputable section

/-- The unit point on the circle used to package the sparse-moment lower bound. -/
def fold_computability_halting_no_computable_modulus_sparse_moments_unit_point : UnitCirclePoint :=
  ⟨1, by simp⟩

/-- Dyadic atomic weight assigned to the `e`-th sparse query. -/
def fold_computability_halting_no_computable_modulus_sparse_moments_dyadic_weight
    (halts : ℕ → Prop) (e : ℕ) : ℚ :=
  by
    classical
    exact if halts e then (((2 : ℚ) ^ e)⁻¹) else 0

/-- A one-atom Lee--Yang package whose recovered atomic mass is the sparse-moment readout attached
to the queried halting index `e`. -/
def fold_computability_halting_no_computable_modulus_sparse_moments_encoding
    (halts : ℕ → Prop) (e : ℕ) : HaltingLeyangEncodingData where
  atomCount := 1
  q := fun _ => e + 1
  atomPoint := fun _ => fold_computability_halting_no_computable_modulus_sparse_moments_unit_point
  atomWeight := fun _ =>
    fold_computability_halting_no_computable_modulus_sparse_moments_dyadic_weight halts e
  circleWeight := 0
  qthRootWitness := by
    intro i
    fin_cases i
    simp [fold_computability_halting_no_computable_modulus_sparse_moments_unit_point]
  supportDisjoint := by
    intro i j hij
    fin_cases i
    fin_cases j
    exact (hij rfl).elim

/-- The sparse moment queried at index `e`, recovered from the one-atom Lee--Yang encoding. -/
def fold_computability_halting_no_computable_modulus_sparse_moments_target
    (halts : ℕ → Prop) (e : ℕ) : ℚ :=
  (fold_computability_halting_no_computable_modulus_sparse_moments_encoding halts e).primeAtomicPart
    fold_computability_halting_no_computable_modulus_sparse_moments_unit_point

/-- The chapter-local sparse-moment modulus claim: if finite-step halting checks are decidable and
the Lee--Yang sparse-moment proxy had a total computable modulus at scale `2^{-e}/6`, then the
global halting predicate would become pointwise decidable. -/
def fold_computability_halting_no_computable_modulus_sparse_moments_statement : Prop :=
  ∀ (haltsWithin : ℕ → ℕ → Prop) (halts : ℕ → Prop),
    RelationPointwiseDecidable haltsWithin →
    (∀ e, halts e ↔ ∃ N, haltsWithin e N) →
    ¬ PredicatePointwiseDecidable halts →
    ¬ ∃ M : ℕ → ℕ,
      ∀ e,
        let target := fold_computability_halting_no_computable_modulus_sparse_moments_target halts e
        let approx : ℚ := by
          classical
          exact if haltsWithin e (M e) then target else 0
        |approx - target| <
          fold_computability_halting_no_computable_modulus_sparse_moments_dyadic_weight halts e / 6

lemma fold_computability_halting_no_computable_modulus_sparse_moments_target_eq
    (halts : ℕ → Prop) (e : ℕ) :
    fold_computability_halting_no_computable_modulus_sparse_moments_target halts e =
      fold_computability_halting_no_computable_modulus_sparse_moments_dyadic_weight halts e := by
  have hrecover :
      (fold_computability_halting_no_computable_modulus_sparse_moments_encoding halts e).atomicRecovery :=
    (paper_fold_computability_halting_leyang_holographic_encoding
      (fold_computability_halting_no_computable_modulus_sparse_moments_encoding halts e)).2.2.2
  simpa [fold_computability_halting_no_computable_modulus_sparse_moments_target,
    fold_computability_halting_no_computable_modulus_sparse_moments_encoding,
    fold_computability_halting_no_computable_modulus_sparse_moments_dyadic_weight] using
    hrecover ⟨0, by simp [fold_computability_halting_no_computable_modulus_sparse_moments_encoding]⟩

lemma fold_computability_halting_no_computable_modulus_sparse_moments_not_small (e : ℕ) :
    ¬ ((((2 : ℚ) ^ e)⁻¹) < (((2 : ℚ) ^ e)⁻¹) / 6) := by
  intro hlt
  have hpos : 0 < (((2 : ℚ) ^ e)⁻¹) := by positivity
  nlinarith

/-- Paper label: `thm:fold-computability-halting-no-computable-modulus-sparse-moments`. -/
theorem paper_fold_computability_halting_no_computable_modulus_sparse_moments :
    fold_computability_halting_no_computable_modulus_sparse_moments_statement := by
  intro haltsWithin halts hStepDec hHalts hUndecidable hM
  apply hUndecidable
  rcases hM with ⟨M, hM⟩
  refine ⟨fun e => ?_⟩
  by_cases hstep : haltsWithin e (M e)
  · exact isTrue ((hHalts e).2 ⟨M e, hstep⟩)
  · refine isFalse ?_
    intro hh
    have hbound := hM e
    have htarget :
        fold_computability_halting_no_computable_modulus_sparse_moments_target halts e =
          (((2 : ℚ) ^ e)⁻¹) := by
      simpa [fold_computability_halting_no_computable_modulus_sparse_moments_dyadic_weight, hh] using
        fold_computability_halting_no_computable_modulus_sparse_moments_target_eq halts e
    have hsmall :
        |(0 : ℚ) -
            fold_computability_halting_no_computable_modulus_sparse_moments_target halts e| <
          (((2 : ℚ) ^ e)⁻¹) / 6 := by
      simpa [hstep, fold_computability_halting_no_computable_modulus_sparse_moments_dyadic_weight,
        hh] using hbound
    have :
        |(0 : ℚ) - (((2 : ℚ) ^ e)⁻¹)| < (((2 : ℚ) ^ e)⁻¹) / 6 := by
      simpa [htarget]
        using hsmall
    have habs :
        (((2 : ℚ) ^ e)⁻¹) < (((2 : ℚ) ^ e)⁻¹) / 6 := by
      simpa using this
    exact fold_computability_halting_no_computable_modulus_sparse_moments_not_small e habs

end

end Omega.Folding
