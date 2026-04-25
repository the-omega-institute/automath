import Omega.Folding.FoldSigmaPhiDiverges

namespace Omega.Folding

/-- Concrete comparison package for promoting the divergence of `Σ_φ` to divergence of the
collision scale. The `hcompare` field records the monotone lower bound from the collision-scale
model against every finite partial sum of the resonance profile. -/
structure FoldCollisionScaleDivergesData where
  Cphi : ℕ → ℝ
  collisionScale : ℕ → ℝ
  c : ℝ
  n0 : ℕ
  hc : 0 < c
  hFib : ∀ n ≥ n0, c ≤ Cphi (Nat.fib n)
  hcompare :
    ∀ m U : ℕ,
      1 + 2 * Finset.sum (Finset.range (U + 1)) (fun u => (Cphi u) ^ 2) ≤
        Nat.fib (m + 2) * collisionScale m

namespace FoldCollisionScaleDivergesData

/-- Divergence of the collision scale after multiplying by the Fibonacci normalization. -/
def collisionScaleDiverges (D : FoldCollisionScaleDivergesData) : Prop :=
  ∀ B : ℝ, ∃ N : ℕ, ∀ m ≥ N, B ≤ Nat.fib (m + 2) * D.collisionScale m

end FoldCollisionScaleDivergesData

open FoldCollisionScaleDivergesData

/-- Paper label: `cor:fold-collision-scale-diverges`. The Fibonacci-frequency lower bound gives
divergence of the resonance partial sums, and the collision-scale lower bound then forces the
normalized collision scale to diverge. -/
theorem paper_fold_collision_scale_diverges (D : FoldCollisionScaleDivergesData) :
    D.collisionScaleDiverges := by
  intro B
  obtain ⟨U, hU⟩ := paper_fold_sigma_phi_diverges D.Cphi D.c D.n0 D.hc D.hFib B
  refine ⟨U, ?_⟩
  intro m hm
  exact le_trans hU (D.hcompare m U)

end Omega.Folding
