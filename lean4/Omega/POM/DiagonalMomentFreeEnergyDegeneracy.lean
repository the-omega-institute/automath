import Omega.POM.DiagonalCollapseQuadraticFreeEnergy

open Filter Topology

namespace Omega.POM

/-- Concrete data for the diagonal free-energy degeneracy statement.  The `O(m)` growth of
`log |X_m|` is encoded by the vanishing of `log |X_m| / m^2`, while the moment sums are
sandwiched between the top fiber contribution and the cardinality-weighted top fiber
contribution. -/
structure pom_diagonal_moment_free_energy_degeneracy_data where
  tau : ℝ
  alphaStar : ℝ
  cardinality : ℕ → ℝ
  maxFiber : ℕ → ℝ
  partitionSum : ℕ → ℝ
  tau_nonneg : 0 ≤ tau
  cardinality_ge_one : ∀ m, 1 ≤ cardinality m
  maxFiber_pos : ∀ m, 0 < maxFiber m
  sandwich :
    ∀ m,
      maxFiber m ^ pomDiagonalMomentIndex tau m ≤ partitionSum m ∧
        partitionSum m ≤ cardinality m * maxFiber m ^ pomDiagonalMomentIndex tau m
  log_cardinality_negligible :
    Tendsto (fun m : ℕ => Real.log (cardinality m) / (m : ℝ) ^ 2) atTop (nhds 0)
  log_maxFiber_limit :
    Tendsto (fun m : ℕ => Real.log (maxFiber m) / (m : ℝ)) atTop (nhds alphaStar)

namespace pom_diagonal_moment_free_energy_degeneracy_data

/-- The diagonal-moment free energy converges to the top-exponent profile `τ α_*`. -/
def statement (D : pom_diagonal_moment_free_energy_degeneracy_data) : Prop :=
  Tendsto (pomDiagonalQuadraticFreeEnergy D.partitionSum) atTop (nhds (D.tau * D.alphaStar))

end pom_diagonal_moment_free_energy_degeneracy_data

/-- `thm:pom-diagonal-moment-free-energy-degeneracy` -/
theorem paper_pom_diagonal_moment_free_energy_degeneracy
    (D : pom_diagonal_moment_free_energy_degeneracy_data) : D.statement := by
  have hsandwich_exp :
      ∀ m,
        Real.exp (((pomDiagonalMomentIndex D.tau m : ℝ)) * Real.log (D.maxFiber m)) ≤
            D.partitionSum m ∧
          D.partitionSum m ≤
            D.cardinality m *
              Real.exp (((pomDiagonalMomentIndex D.tau m : ℝ)) * Real.log (D.maxFiber m)) := by
    intro m
    have hexp_eq :
        Real.exp (((pomDiagonalMomentIndex D.tau m : ℝ)) * Real.log (D.maxFiber m)) =
          D.maxFiber m ^ pomDiagonalMomentIndex D.tau m := by
      calc
        Real.exp (((pomDiagonalMomentIndex D.tau m : ℝ)) * Real.log (D.maxFiber m))
            = Real.exp (pomDiagonalMomentIndex D.tau m * Real.log (D.maxFiber m)) := by
                simp
        _ = Real.exp (Real.log (D.maxFiber m)) ^ pomDiagonalMomentIndex D.tau m := by
              rw [Real.exp_nat_mul]
        _ = D.maxFiber m ^ pomDiagonalMomentIndex D.tau m := by
              rw [Real.exp_log (D.maxFiber_pos m)]
    rcases D.sandwich m with ⟨hlower, hupper⟩
    exact ⟨by simpa [hexp_eq] using hlower, by simpa [hexp_eq] using hupper⟩
  simpa [pom_diagonal_moment_free_energy_degeneracy_data.statement] using
    paper_pom_diagonal_collapse_quadratic_free_energy
      D.cardinality
      D.maxFiber
      D.partitionSum
      D.tau
      D.alphaStar
      D.tau_nonneg
      D.cardinality_ge_one
      hsandwich_exp
      D.log_cardinality_negligible
      D.log_maxFiber_limit

end Omega.POM
