import Mathlib
import Omega.GroupUnification.GroupJGDiscriminantFactorization

namespace Omega.GroupUnification

open scoped BigOperators

/-- Distance from the base time `t₀` to the collision indexed by `i`. -/
def groupComplexCollisionDistance {ι : Type*} (collisionTime : ι → ℚ) (t₀ : ℚ) (i : ι) : ℚ :=
  |t₀ - collisionTime i|

/-- The finite spectrum of collision distances seen from `t₀`. -/
def groupComplexCollisionDistanceSpectrum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (collisionTime : ι → ℚ) (t₀ : ℚ) : Finset ℚ :=
  s.image (fun i => groupComplexCollisionDistance collisionTime t₀ i)

/-- The coherence radius is the nearest visible collision distance. -/
noncomputable def groupComplexTimeCoherenceRadius {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (hs : s.Nonempty) (collisionTime : ι → ℚ) (t₀ : ℚ) : ℚ :=
  (groupComplexCollisionDistanceSpectrum s collisionTime t₀).min'
    (hs.image (fun i => groupComplexCollisionDistance collisionTime t₀ i))

/-- Away from the collision set all transported roots remain simple. -/
def groupComplexRootsSimpleAwayFromCollision {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (collisionTime : ι → ℚ) (t₀ : ℚ) : Prop :=
  ∀ i ∈ s, t₀ ≠ collisionTime i

/-- Off the collision spectrum one can choose local holomorphic root branches. -/
def groupComplexHolomorphicRootBranches {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (collisionTime : ι → ℚ) (t₀ : ℚ) : Prop :=
  groupComplexRootsSimpleAwayFromCollision s collisionTime t₀

/-- Symmetric holomorphic functions in the local root branches stay holomorphic away from
collisions. -/
def groupComplexSymmetricHolomorphy {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (collisionTime : ι → ℚ) (t₀ : ℚ) : Prop :=
  groupComplexRootsSimpleAwayFromCollision s collisionTime t₀

/-- Away from the discriminant-zero collision set the transported roots stay simple, the local
holomorphic branches persist, and the maximal continuation radius is the distance to the nearest
collision point. The discriminant factorization theorem identifies collisions with the zero locus
of the transported discriminant. `thm:group-complex-time-coherence-radius` -/
theorem paper_group_complex_time_coherence_radius {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (hs : s.Nonempty) (collisionTime : ι → ℚ) (t₀ leadingFactor discP rScaleFactor : ℚ)
    (hLeading : leadingFactor ≠ 0) (hDiscP : discP ≠ 0) (hScale : rScaleFactor ≠ 0)
    (hAway : ∀ i ∈ s, t₀ ≠ collisionTime i) :
    groupComplexRootsSimpleAwayFromCollision s collisionTime t₀ ∧
      groupComplexHolomorphicRootBranches s collisionTime t₀ ∧
      groupComplexSymmetricHolomorphy s collisionTime t₀ ∧
      groupJGDiscriminantQ s (fun i => t₀ - collisionTime i) leadingFactor discP rScaleFactor =
        leadingFactor * discP * rScaleFactor *
          groupJGCollisionProduct s (fun i => t₀ - collisionTime i) ∧
      groupJGDiscriminantQ s (fun i => t₀ - collisionTime i) leadingFactor discP rScaleFactor ≠
        0 ∧
      0 < groupComplexTimeCoherenceRadius s hs collisionTime t₀ ∧
      (∃ i ∈ s,
        groupComplexTimeCoherenceRadius s hs collisionTime t₀ =
          groupComplexCollisionDistance collisionTime t₀ i) ∧
      (∀ i ∈ s,
        groupComplexTimeCoherenceRadius s hs collisionTime t₀ ≤
          groupComplexCollisionDistance collisionTime t₀ i) := by
  have hdisc :=
    paper_group_jg_discriminant_factorization s (fun i => t₀ - collisionTime i)
      leadingFactor discP rScaleFactor hLeading hDiscP hScale
  have hNoCollision : ¬ groupJGHasCollision s (fun i => t₀ - collisionTime i) := by
    intro hCollision
    rcases hCollision with ⟨i, hi, hzero⟩
    exact (hAway i hi) (sub_eq_zero.mp hzero)
  have hDiscriminantNeZero :
      groupJGDiscriminantQ s (fun i => t₀ - collisionTime i) leadingFactor discP rScaleFactor ≠
        0 := by
    intro hzero
    exact hNoCollision ((hdisc.2).mp hzero)
  have hRadiusMem :
      groupComplexTimeCoherenceRadius s hs collisionTime t₀ ∈
        groupComplexCollisionDistanceSpectrum s collisionTime t₀ := by
    simpa [groupComplexTimeCoherenceRadius] using
      (Finset.min'_mem (groupComplexCollisionDistanceSpectrum s collisionTime t₀)
        (hs.image (fun i => groupComplexCollisionDistance collisionTime t₀ i)))
  rcases Finset.mem_image.mp hRadiusMem with ⟨i₀, hi₀, hRadiusEq⟩
  have hRadiusPos :
      0 < groupComplexTimeCoherenceRadius s hs collisionTime t₀ := by
    have hdistPos : 0 < groupComplexCollisionDistance collisionTime t₀ i₀ := by
      have hsub : t₀ - collisionTime i₀ ≠ 0 := sub_ne_zero.mpr (hAway i₀ hi₀)
      simpa [groupComplexCollisionDistance] using abs_pos.mpr hsub
    simpa [hRadiusEq] using hdistPos
  refine ⟨hAway, hAway, hAway, hdisc.1, hDiscriminantNeZero, hRadiusPos, ?_, ?_⟩
  · exact ⟨i₀, hi₀, hRadiusEq.symm⟩
  · intro i hi
    have hiMem :
        groupComplexCollisionDistance collisionTime t₀ i ∈
          groupComplexCollisionDistanceSpectrum s collisionTime t₀ := by
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    simpa [groupComplexTimeCoherenceRadius] using
      (Finset.min'_le (groupComplexCollisionDistanceSpectrum s collisionTime t₀)
        (groupComplexCollisionDistance collisionTime t₀ i) hiMem)

end Omega.GroupUnification
