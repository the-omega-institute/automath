import Omega.Folding.FoldCollisionZeroSparsityImpact
import Omega.Folding.KilloFoldRenyi2UniformityGap

namespace Omega.Zeta

/-- Zero-block corrections stay on the sparse side, while the max-fiber witness retains a fixed
positive uniformity gap. -/
def xi_time_part9zoa_zero_block_maxfiber_impotence_statement (m : ℕ) : Prop :=
  0 < Omega.Folding.killoFoldUniformityGap ∧
    (Even (Nat.fib (m + 2)) →
      let M := Nat.fib (m + 2)
      let h := (m + 2) / 2
      let Z := Omega.Folding.foldZeroFrequencyUnion m
      (Z.card : ℚ) / M ≤ ((((m + 2).divisors.card * Nat.fib h : ℕ) : ℚ) / M) ∧
        (Z.card : ℚ) / M ≤ (((m + 2).divisors.card : ℕ) : ℚ) / Nat.fib (h + 1))

/-- Verification theorem for the zero-block/max-fiber separation package. -/
theorem xi_time_part9zoa_zero_block_maxfiber_impotence_verified (m : ℕ) :
    xi_time_part9zoa_zero_block_maxfiber_impotence_statement m := by
  refine ⟨(Omega.Folding.paper_killo_fold_renyi2_uniformity_gap).2.2, ?_⟩
  intro hEven
  simpa [xi_time_part9zoa_zero_block_maxfiber_impotence_statement] using
    Omega.Folding.paper_fold_collision_zero_sparsity_impact m hEven

/-- Paper label: `thm:xi-time-part9zoa-zero-block-maxfiber-impotence`. -/
def paper_xi_time_part9zoa_zero_block_maxfiber_impotence (m : ℕ) : Prop := by
  exact xi_time_part9zoa_zero_block_maxfiber_impotence_statement m

end Omega.Zeta
