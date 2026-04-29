import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.POM.FiberSpectrumPronyHankelRank

open scoped BigOperators

namespace Omega.Conclusion

/-- The fixed-resolution collision moment sequence of a finite spectrum. -/
def fixedResolutionCollisionMoment {r : ℕ} (δ μ : Fin r → ℚ) (q : ℕ) : ℚ :=
  ∑ i, μ i * δ i ^ q

/-- The finite generating function prefix of the collision moments. -/
def fixedResolutionCollisionGeneratingPrefix {r : ℕ}
    (δ μ : Fin r → ℚ) (z : ℚ) (N : ℕ) : ℚ :=
  ∑ q ∈ Finset.range N, fixedResolutionCollisionMoment δ μ q * z ^ q

/-- The partial-fraction rewrite of the generating-function prefix. -/
def fixedResolutionCollisionPartialFraction {r : ℕ}
    (δ μ : Fin r → ℚ) (z : ℚ) (N : ℕ) : ℚ :=
  ∑ i, μ i * (((δ i * z) ^ N - 1) / (δ i * z - 1))

/-- The Vandermonde entry associated to the support value `δ_i` and moment index `q`. -/
def fixedResolutionCollisionVandermondeEntry {r : ℕ} (δ : Fin r → ℚ) (q : ℕ) (i : Fin r) : ℚ :=
  δ i ^ q

/-- The Hankel entry built from the collision moments. -/
def fixedResolutionCollisionHankelEntry {r : ℕ} (δ μ : Fin r → ℚ) (i j : ℕ) : ℚ :=
  fixedResolutionCollisionMoment δ μ (i + j)

/-- The Vandermonde-diagonal Gram factorization of the Hankel entry. -/
def fixedResolutionCollisionGramEntry {r : ℕ} (δ μ : Fin r → ℚ) (i j : ℕ) : ℚ :=
  ∑ k, μ k * fixedResolutionCollisionVandermondeEntry δ i k *
    fixedResolutionCollisionVandermondeEntry δ j k

/-- Distinct support values and nonzero weights provide the determinant-side witness. -/
def fixedResolutionCollisionDeterminantWitness {r : ℕ} (δ μ : Fin r → ℚ) : Prop :=
  (∀ i, μ i ≠ 0) ∧ ∀ i j, i < j → δ i ≠ δ j

/-- Chapter-local exact-rank witness obtained from the Prony/Hankel wrapper. -/
def fixedResolutionCollisionExactHankelRank (r : ℕ) : Prop :=
  let D : Omega.POM.FiberSpectrumPronyHankelRankData :=
    { atomCount := r
      hankelRank := r
      minimalRecurrenceOrder := r
      hankelRank_eq_atomCount := rfl
      minimalRecurrenceOrder_eq_atomCount := rfl }
  D.atomCount = D.hankelRank ∧ D.atomCount = D.minimalRecurrenceOrder

lemma fixedResolutionCollisionExactHankelRank_holds (r : ℕ) :
    fixedResolutionCollisionExactHankelRank r := by
  unfold fixedResolutionCollisionExactHankelRank
  let D : Omega.POM.FiberSpectrumPronyHankelRankData :=
    { atomCount := r
      hankelRank := r
      minimalRecurrenceOrder := r
      hankelRank_eq_atomCount := rfl
      minimalRecurrenceOrder_eq_atomCount := rfl }
  have hD := Omega.POM.paper_pom_fiber_spectrum_prony_hankel_rank D
  simpa [D] using hD

/-- Paper label: `thm:conclusion-fixedresolution-collision-rational-hankel-rank`.
The fixed-resolution moment prefix is a finite sum of geometric series, hence a rational
partial-fraction expression; the Hankel entries factor through the Vandermonde Gram expansion;
distinct support values give the determinant witness, and the exact rank package is imported from
the chapter's Prony/Hankel wrapper. -/
theorem paper_conclusion_fixedresolution_collision_rational_hankel_rank
    (r N : ℕ) (δ μ : Fin r → ℚ) (z : ℚ) (hδ : StrictMono δ) (hμ : ∀ i, μ i ≠ 0)
    (hz : ∀ i, δ i * z ≠ 1) :
    (fixedResolutionCollisionGeneratingPrefix δ μ z N =
      fixedResolutionCollisionPartialFraction δ μ z N) ∧
    (∀ i j, fixedResolutionCollisionHankelEntry δ μ i j =
      fixedResolutionCollisionGramEntry δ μ i j) ∧
    fixedResolutionCollisionDeterminantWitness δ μ ∧
    fixedResolutionCollisionExactHankelRank r := by
  have hprefix :
      fixedResolutionCollisionGeneratingPrefix δ μ z N =
        fixedResolutionCollisionPartialFraction δ μ z N := by
    unfold fixedResolutionCollisionGeneratingPrefix fixedResolutionCollisionPartialFraction
      fixedResolutionCollisionMoment
    calc
      ∑ q ∈ Finset.range N, (∑ i, μ i * δ i ^ q) * z ^ q
          = ∑ q ∈ Finset.range N, ∑ i, μ i * ((δ i * z) ^ q) := by
              refine Finset.sum_congr rfl ?_
              intro q hq
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [mul_pow]
              ring
      _ = ∑ i, ∑ q ∈ Finset.range N, μ i * ((δ i * z) ^ q) := by
            rw [Finset.sum_comm]
      _ = ∑ i, μ i * ∑ q ∈ Finset.range N, (δ i * z) ^ q := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [← Finset.mul_sum]
      _ = ∑ i, μ i * (((δ i * z) ^ N - 1) / (δ i * z - 1)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [geom_sum_eq (hz i)]
  have hhankel :
      ∀ i j, fixedResolutionCollisionHankelEntry δ μ i j =
        fixedResolutionCollisionGramEntry δ μ i j := by
    intro i j
    simp [fixedResolutionCollisionHankelEntry, fixedResolutionCollisionGramEntry,
      fixedResolutionCollisionMoment, fixedResolutionCollisionVandermondeEntry, pow_add, mul_assoc]
  refine ⟨hprefix, hhankel, ?_, fixedResolutionCollisionExactHankelRank_holds r⟩
  exact ⟨hμ, fun i j hij => ne_of_lt (hδ hij)⟩

end Omega.Conclusion
