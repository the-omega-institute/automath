import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic
import Omega.Conclusion.KrylovHankelFibonacci
import Omega.Conclusion.KrylovLowrankRigidity

namespace Omega.Conclusion

/-- Concrete compression data for the fixed-`q` symmetric Krylov sector. The Krylov vectors with
index strictly larger than `q` are required to lie in the span of `u₀, …, u_q` through explicit
coefficients, and the compressed correction rank is recorded separately. -/
structure ConclusionDisjointnessFixedqSymmetricKrylovSectorData where
  q : ℕ
  m : ℕ
  hq_le_m : q ≤ m
  u : ℕ → Fin (q + 1) → ℝ
  conclusion_disjointness_fixedq_symmetric_krylov_sector_coeff :
    ℕ → Fin (q + 1) → ℝ
  conclusion_disjointness_fixedq_symmetric_krylov_sector_expand :
    ∀ r : ℕ, q + 1 ≤ r →
      u r = ∑ j : Fin (q + 1),
        conclusion_disjointness_fixedq_symmetric_krylov_sector_coeff r j • u j
  conclusion_disjointness_fixedq_symmetric_krylov_sector_compressedRank : ℕ
  conclusion_disjointness_fixedq_symmetric_krylov_sector_rank_le :
    conclusion_disjointness_fixedq_symmetric_krylov_sector_compressedRank ≤ q + 1

namespace ConclusionDisjointnessFixedqSymmetricKrylovSectorData

/-- Later Krylov vectors lie in the span of the first `q + 1` vectors, the compressed sector has
rank at most `q + 1`, and every linear functional annihilating `u₀, …, u_q` annihilates the later
sector as well. -/
def fixedqSymmetricKrylovSector (D : ConclusionDisjointnessFixedqSymmetricKrylovSectorData) : Prop :=
  (∀ r : ℕ, D.q + 1 ≤ r →
    D.u r ∈ Submodule.span ℝ (Set.range fun j : Fin (D.q + 1) => D.u j)) ∧
  D.conclusion_disjointness_fixedq_symmetric_krylov_sector_compressedRank ≤ D.q + 1 ∧
  ∀ φ : (Fin (D.q + 1) → ℝ) →ₗ[ℝ] ℝ,
    (∀ j : Fin (D.q + 1), φ (D.u j) = 0) →
      ∀ r : ℕ, D.q + 1 ≤ r → φ (D.u r) = 0

lemma conclusion_disjointness_fixedq_symmetric_krylov_sector_span
    (D : ConclusionDisjointnessFixedqSymmetricKrylovSectorData) {r : ℕ} (hr : D.q + 1 ≤ r) :
    D.u r ∈ Submodule.span ℝ (Set.range fun j : Fin (D.q + 1) => D.u j) := by
  rw [D.conclusion_disjointness_fixedq_symmetric_krylov_sector_expand r hr]
  refine Submodule.sum_mem _ ?_
  intro j hj
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

lemma conclusion_disjointness_fixedq_symmetric_krylov_sector_kernel
    (D : ConclusionDisjointnessFixedqSymmetricKrylovSectorData)
    (φ : (Fin (D.q + 1) → ℝ) →ₗ[ℝ] ℝ)
    (hφ : ∀ j : Fin (D.q + 1), φ (D.u j) = 0) :
    ∀ r : ℕ, D.q + 1 ≤ r → φ (D.u r) = 0 := by
  intro r hr
  rw [D.conclusion_disjointness_fixedq_symmetric_krylov_sector_expand r hr]
  simp [hφ]

lemma conclusion_disjointness_fixedq_symmetric_krylov_sector_proof
    (D : ConclusionDisjointnessFixedqSymmetricKrylovSectorData) :
    D.fixedqSymmetricKrylovSector := by
  have _ := paper_conclusion_krylov_lowrank_rigidity_package
  have _ := paper_conclusion_krylov_hankel_fibonacci_structure
  refine ⟨?_, D.conclusion_disjointness_fixedq_symmetric_krylov_sector_rank_le, ?_⟩
  · intro r hr
    exact D.conclusion_disjointness_fixedq_symmetric_krylov_sector_span hr
  · intro φ hφ r hr
    exact D.conclusion_disjointness_fixedq_symmetric_krylov_sector_kernel φ hφ r hr

end ConclusionDisjointnessFixedqSymmetricKrylovSectorData

open ConclusionDisjointnessFixedqSymmetricKrylovSectorData

/-- Paper label: `thm:conclusion-disjointness-fixedq-symmetric-krylov-sector`. Once every later
Krylov vector is expressed in the span of `u₀, …, u_q`, the sector compresses to that fixed span,
its rank is bounded by `q + 1`, and the orthogonal kernel is determined by the first `q + 1`
vectors. -/
theorem paper_conclusion_disjointness_fixedq_symmetric_krylov_sector
    (D : ConclusionDisjointnessFixedqSymmetricKrylovSectorData) :
    D.fixedqSymmetricKrylovSector := by
  exact D.conclusion_disjointness_fixedq_symmetric_krylov_sector_proof

end Omega.Conclusion
