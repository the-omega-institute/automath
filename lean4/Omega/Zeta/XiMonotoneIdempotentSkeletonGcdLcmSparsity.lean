import Mathlib.Data.Set.PowersetCard
import Mathlib.Tactic
import Omega.Zeta.PrimeRegisterIdempotentExactCount
import Omega.Zeta.XiChainIdempotentStarSaturationComparableGcd

namespace Omega.Zeta

/-- The monotone skeleton keeps the forced base coordinate and records the remaining `k - 1`
free fixed points. -/
def monotoneSkeletonRankFamily (n k : ℕ) : Finset (Finset (Fin (n - 1))) :=
  (Finset.univ : Finset (Fin (n - 1))).powersetCard (k - 1)

/-- Rank-`k` monotone skeleton count. -/
def monotoneSkeletonRankCount (n k : ℕ) : ℕ :=
  (monotoneSkeletonRankFamily n k).card

/-- Comparable-chain meet on the monotone skeleton. -/
def monotoneSkeletonMeet {n : ℕ} (F G : Finset (Fin (n - 1))) : Finset (Fin (n - 1)) :=
  chainIdempotentProduct F G

/-- Join on the monotone skeleton is set-theoretic union of the free coordinates. -/
def monotoneSkeletonJoin {n : ℕ} (F G : Finset (Fin (n - 1))) : Finset (Fin (n - 1)) :=
  F ∪ G

/-- The arithmetic shadow inherited from the chain-interior model. -/
def monotoneSkeletonShadow {n : ℕ} (F : Finset (Fin (n - 1))) : ℕ :=
  primeSupportProduct F

/-- The ratio between rank-`k` monotone skeletons and all rank-`k` prime-register idempotents. -/
def monotoneSkeletonSparsityRatio (n k : ℕ) : ℚ :=
  (monotoneSkeletonRankCount n k : ℚ) / (primeRegisterIdempotentCount n k : ℚ)

lemma monotoneSkeletonRankCount_eq_choose (n k : ℕ) :
    monotoneSkeletonRankCount n k = Nat.choose (n - 1) (k - 1) := by
  simp [monotoneSkeletonRankCount, monotoneSkeletonRankFamily, Finset.card_powersetCard]

lemma monotoneSkeletonJoin_lcm_of_subset {n : ℕ} {F G : Finset (Fin (n - 1))} (hFG : F ⊆ G) :
    monotoneSkeletonShadow (monotoneSkeletonJoin F G) =
      Nat.lcm (monotoneSkeletonShadow F) (monotoneSkeletonShadow G) := by
  have hUnion : monotoneSkeletonJoin F G = G := Finset.union_eq_right.mpr hFG
  rw [hUnion]
  exact (Nat.lcm_eq_right (primeSupportProduct_mono hFG)).symm

lemma monotoneSkeletonJoin_lcm_of_superset {n : ℕ} {F G : Finset (Fin (n - 1))} (hGF : G ⊆ F) :
    monotoneSkeletonShadow (monotoneSkeletonJoin F G) =
      Nat.lcm (monotoneSkeletonShadow F) (monotoneSkeletonShadow G) := by
  have hUnion : monotoneSkeletonJoin F G = F := Finset.union_eq_left.mpr hGF
  rw [hUnion]
  exact (Nat.lcm_eq_left (primeSupportProduct_mono hGF)).symm

/-- Paper label: `thm:xi-monotone-idempotent-skeleton-gcd-lcm-sparsity`.
The monotone idempotent skeleton inherits the Boolean meet/join transport from the comparable
chain-interior model, its free rank-`k` stratum has size `choose (n - 1) (k - 1)`, and the
resulting sparsity ratio is the quotient by the exact prime-register idempotent count. -/
theorem paper_xi_monotone_idempotent_skeleton_gcd_lcm_sparsity (n k : ℕ) :
    (∀ F G : Finset (Fin (n - 1)), F ⊆ G ∨ G ⊆ F →
        monotoneSkeletonMeet F G = F ∩ G ∧ monotoneSkeletonJoin F G = F ∪ G) ∧
      (∀ F G : Finset (Fin (n - 1)), F ⊆ G ∨ G ⊆ F →
        monotoneSkeletonShadow (monotoneSkeletonMeet F G) =
            Nat.gcd (monotoneSkeletonShadow F) (monotoneSkeletonShadow G) ∧
          monotoneSkeletonShadow (monotoneSkeletonJoin F G) =
            Nat.lcm (monotoneSkeletonShadow F) (monotoneSkeletonShadow G)) ∧
      monotoneSkeletonRankCount n k = Nat.choose (n - 1) (k - 1) ∧
      monotoneSkeletonSparsityRatio n k =
        (Nat.choose (n - 1) (k - 1) : ℚ) / (Nat.choose n k * k ^ (n - k) : ℚ) := by
  refine ⟨?_, ?_, monotoneSkeletonRankCount_eq_choose n k, ?_⟩
  · intro F G hcomp
    refine ⟨chainIdempotentProduct_eq_inter F G, rfl⟩
  · intro F G hcomp
    refine ⟨?_, ?_⟩
    · calc
        monotoneSkeletonShadow (monotoneSkeletonMeet F G)
            = primeSupportProduct (chainIdempotentProduct F G) := by
                rfl
        _ = primeSupportProduct (F ∩ G) := by rw [chainIdempotentProduct_eq_inter]
        _ = Nat.gcd (monotoneSkeletonShadow F) (monotoneSkeletonShadow G) := by
              simpa [monotoneSkeletonShadow] using
                paper_xi_chain_idempotent_star_saturation_comparable_gcd F G hcomp |>.2
    · rcases hcomp with hFG | hGF
      · exact monotoneSkeletonJoin_lcm_of_subset hFG
      · exact monotoneSkeletonJoin_lcm_of_superset hGF
  · simp [monotoneSkeletonSparsityRatio, monotoneSkeletonRankCount_eq_choose,
      primeRegisterIdempotentCount]

end Omega.Zeta
