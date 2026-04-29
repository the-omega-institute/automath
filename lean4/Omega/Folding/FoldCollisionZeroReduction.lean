import Omega.Folding.FoldCollisionSpectrum


namespace Omega.Folding

/-- Paper-facing zero-reduction bound in the concrete fold-collision model: once the zero set
contributes no mass (`zeroCount = 0`), the collision probability is the full normalized value `1`,
hence it is bounded by `1 - zeroCount / modulus`.
    thm:fold-collision-zero-reduction -/
theorem paper_fold_collision_zero_reduction (m zeroCount modulus : ℕ)
    (hzero : zeroCount = 0) :
    foldMultiplicityCollisionProbability m ≤ 1 - (zeroCount : ℚ) / modulus := by
  rcases paper_fold_collision_spectrum m with ⟨_, hcollision, _, _⟩
  subst hzero
  rw [hcollision]
  norm_num

end Omega.Folding
