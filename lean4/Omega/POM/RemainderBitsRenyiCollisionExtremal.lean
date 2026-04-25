import Omega.Conclusion.BalancedExternalizationOptimalRenyiEnergy
import Omega.Conclusion.BalancedExternalizationSchurOptimality

namespace Omega.POM

/-- Paper-facing remainder-bit extremal package: the balanced occupancy profile minimizes the
fiberwise `q`-power sum among the audited redistributions, and the existing Schur-optimality
certificate records the Robin-Hood transfer, balanced support profile, and doubly stochastic
witness. -/
def pom_remainder_bits_renyi_collision_extremal_statement : Prop :=
  (∀ {α : Type*} [DecidableEq α] (X : Finset α) (d : α → ℕ) (B q : ℕ), 1 ≤ q →
    Omega.Conclusion.conclusion_balanced_externalization_optimal_renyi_energy_statement X d B q) ∧
  (∀ F M : ℕ,
    let b := Omega.Zeta.xiTimePart64baBalancedProfile F M
    (∀ x y : ℤ, y + 2 ≤ x →
      (x - 1) + (y + 1) = x + y ∧ (x - 1) ^ 2 + (y + 1) ^ 2 < x ^ 2 + y ^ 2) ∧
      (∀ i, b i = M / F ∨ b i = M / F + 1) ∧
      (∀ i j, Int.natAbs ((b i : ℤ) - b j) ≤ 1) ∧
      Omega.Zeta.xiTimePart64baDoublyStochastic (1 : Matrix (Fin F) (Fin F) ℚ) ∧
      (Matrix.mulVec (1 : Matrix (Fin F) (Fin F) ℚ) (fun i => (b i : ℚ)) = fun i => (b i : ℚ)))

theorem paper_pom_remainder_bits_renyi_collision_extremal :
    pom_remainder_bits_renyi_collision_extremal_statement := by
  refine ⟨?_, ?_⟩
  · intro α _ X d B q hq
    exact Omega.Conclusion.paper_conclusion_balanced_externalization_optimal_renyi_energy
      X d B q hq
  · intro F M
    simpa using
      (Omega.Conclusion.paper_conclusion_balanced_externalization_schur_optimality
        (F := F) (M := M))

end Omega.POM
