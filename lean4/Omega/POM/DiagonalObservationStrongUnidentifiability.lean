import Omega.POM.DiagonalMomentFreeEnergyDegeneracy

open Filter Topology

namespace Omega.POM

/-- Concrete data for diagonal-observation strong unidentifiability: two diagonal moment spectra
share the same top exponent while their fixed-order collision scales remain separated. -/
structure pom_diagonal_observation_strong_unidentifiability_data where
  pom_diagonal_observation_strong_unidentifiability_tau : ℝ
  pom_diagonal_observation_strong_unidentifiability_alphaStar : ℝ
  pom_diagonal_observation_strong_unidentifiability_leftCardinality : ℕ → ℝ
  pom_diagonal_observation_strong_unidentifiability_leftMaxFiber : ℕ → ℝ
  pom_diagonal_observation_strong_unidentifiability_leftPartitionSum : ℕ → ℝ
  pom_diagonal_observation_strong_unidentifiability_rightCardinality : ℕ → ℝ
  pom_diagonal_observation_strong_unidentifiability_rightMaxFiber : ℕ → ℝ
  pom_diagonal_observation_strong_unidentifiability_rightPartitionSum : ℕ → ℝ
  pom_diagonal_observation_strong_unidentifiability_fixedOrder : ℕ
  pom_diagonal_observation_strong_unidentifiability_remainingMass : ℝ
  pom_diagonal_observation_strong_unidentifiability_diffuseBins : ℕ
  pom_diagonal_observation_strong_unidentifiability_tau_nonneg :
    0 ≤ pom_diagonal_observation_strong_unidentifiability_tau
  pom_diagonal_observation_strong_unidentifiability_leftCardinality_ge_one :
    ∀ m, 1 ≤ pom_diagonal_observation_strong_unidentifiability_leftCardinality m
  pom_diagonal_observation_strong_unidentifiability_leftMaxFiber_pos :
    ∀ m, 0 < pom_diagonal_observation_strong_unidentifiability_leftMaxFiber m
  pom_diagonal_observation_strong_unidentifiability_leftSandwich :
    ∀ m,
      pom_diagonal_observation_strong_unidentifiability_leftMaxFiber m ^
          pomDiagonalMomentIndex
            pom_diagonal_observation_strong_unidentifiability_tau m ≤
        pom_diagonal_observation_strong_unidentifiability_leftPartitionSum m ∧
      pom_diagonal_observation_strong_unidentifiability_leftPartitionSum m ≤
        pom_diagonal_observation_strong_unidentifiability_leftCardinality m *
          pom_diagonal_observation_strong_unidentifiability_leftMaxFiber m ^
            pomDiagonalMomentIndex
              pom_diagonal_observation_strong_unidentifiability_tau m
  pom_diagonal_observation_strong_unidentifiability_leftLogCardinality_negligible :
    Tendsto
      (fun m : ℕ =>
        Real.log (pom_diagonal_observation_strong_unidentifiability_leftCardinality m) /
          (m : ℝ) ^ 2)
      atTop (nhds 0)
  pom_diagonal_observation_strong_unidentifiability_leftLogMaxFiber_limit :
    Tendsto
      (fun m : ℕ =>
        Real.log (pom_diagonal_observation_strong_unidentifiability_leftMaxFiber m) / (m : ℝ))
      atTop (nhds pom_diagonal_observation_strong_unidentifiability_alphaStar)
  pom_diagonal_observation_strong_unidentifiability_rightCardinality_ge_one :
    ∀ m, 1 ≤ pom_diagonal_observation_strong_unidentifiability_rightCardinality m
  pom_diagonal_observation_strong_unidentifiability_rightMaxFiber_pos :
    ∀ m, 0 < pom_diagonal_observation_strong_unidentifiability_rightMaxFiber m
  pom_diagonal_observation_strong_unidentifiability_rightSandwich :
    ∀ m,
      pom_diagonal_observation_strong_unidentifiability_rightMaxFiber m ^
          pomDiagonalMomentIndex
            pom_diagonal_observation_strong_unidentifiability_tau m ≤
        pom_diagonal_observation_strong_unidentifiability_rightPartitionSum m ∧
      pom_diagonal_observation_strong_unidentifiability_rightPartitionSum m ≤
        pom_diagonal_observation_strong_unidentifiability_rightCardinality m *
          pom_diagonal_observation_strong_unidentifiability_rightMaxFiber m ^
            pomDiagonalMomentIndex
              pom_diagonal_observation_strong_unidentifiability_tau m
  pom_diagonal_observation_strong_unidentifiability_rightLogCardinality_negligible :
    Tendsto
      (fun m : ℕ =>
        Real.log (pom_diagonal_observation_strong_unidentifiability_rightCardinality m) /
          (m : ℝ) ^ 2)
      atTop (nhds 0)
  pom_diagonal_observation_strong_unidentifiability_rightLogMaxFiber_limit :
    Tendsto
      (fun m : ℕ =>
        Real.log (pom_diagonal_observation_strong_unidentifiability_rightMaxFiber m) / (m : ℝ))
      atTop (nhds pom_diagonal_observation_strong_unidentifiability_alphaStar)
  pom_diagonal_observation_strong_unidentifiability_collisionScale_separated :
    pom_diagonal_observation_strong_unidentifiability_remainingMass ^
        pom_diagonal_observation_strong_unidentifiability_fixedOrder ≠
      (pom_diagonal_observation_strong_unidentifiability_remainingMass /
          (pom_diagonal_observation_strong_unidentifiability_diffuseBins + 1 : ℝ)) ^
        pom_diagonal_observation_strong_unidentifiability_fixedOrder

namespace pom_diagonal_observation_strong_unidentifiability_data

noncomputable def pom_diagonal_observation_strong_unidentifiability_leftData
    (D : pom_diagonal_observation_strong_unidentifiability_data) :
    pom_diagonal_moment_free_energy_degeneracy_data where
  tau := D.pom_diagonal_observation_strong_unidentifiability_tau
  alphaStar := D.pom_diagonal_observation_strong_unidentifiability_alphaStar
  cardinality := D.pom_diagonal_observation_strong_unidentifiability_leftCardinality
  maxFiber := D.pom_diagonal_observation_strong_unidentifiability_leftMaxFiber
  partitionSum := D.pom_diagonal_observation_strong_unidentifiability_leftPartitionSum
  tau_nonneg := D.pom_diagonal_observation_strong_unidentifiability_tau_nonneg
  cardinality_ge_one :=
    D.pom_diagonal_observation_strong_unidentifiability_leftCardinality_ge_one
  maxFiber_pos := D.pom_diagonal_observation_strong_unidentifiability_leftMaxFiber_pos
  sandwich := D.pom_diagonal_observation_strong_unidentifiability_leftSandwich
  log_cardinality_negligible :=
    D.pom_diagonal_observation_strong_unidentifiability_leftLogCardinality_negligible
  log_maxFiber_limit :=
    D.pom_diagonal_observation_strong_unidentifiability_leftLogMaxFiber_limit

noncomputable def pom_diagonal_observation_strong_unidentifiability_rightData
    (D : pom_diagonal_observation_strong_unidentifiability_data) :
    pom_diagonal_moment_free_energy_degeneracy_data where
  tau := D.pom_diagonal_observation_strong_unidentifiability_tau
  alphaStar := D.pom_diagonal_observation_strong_unidentifiability_alphaStar
  cardinality := D.pom_diagonal_observation_strong_unidentifiability_rightCardinality
  maxFiber := D.pom_diagonal_observation_strong_unidentifiability_rightMaxFiber
  partitionSum := D.pom_diagonal_observation_strong_unidentifiability_rightPartitionSum
  tau_nonneg := D.pom_diagonal_observation_strong_unidentifiability_tau_nonneg
  cardinality_ge_one :=
    D.pom_diagonal_observation_strong_unidentifiability_rightCardinality_ge_one
  maxFiber_pos := D.pom_diagonal_observation_strong_unidentifiability_rightMaxFiber_pos
  sandwich := D.pom_diagonal_observation_strong_unidentifiability_rightSandwich
  log_cardinality_negligible :=
    D.pom_diagonal_observation_strong_unidentifiability_rightLogCardinality_negligible
  log_maxFiber_limit :=
    D.pom_diagonal_observation_strong_unidentifiability_rightLogMaxFiber_limit

noncomputable def pom_diagonal_observation_strong_unidentifiability_concentratedScale
    (D : pom_diagonal_observation_strong_unidentifiability_data) : ℝ :=
  D.pom_diagonal_observation_strong_unidentifiability_remainingMass ^
    D.pom_diagonal_observation_strong_unidentifiability_fixedOrder

noncomputable def pom_diagonal_observation_strong_unidentifiability_diffuseScale
    (D : pom_diagonal_observation_strong_unidentifiability_data) : ℝ :=
  (D.pom_diagonal_observation_strong_unidentifiability_remainingMass /
      (D.pom_diagonal_observation_strong_unidentifiability_diffuseBins + 1 : ℝ)) ^
    D.pom_diagonal_observation_strong_unidentifiability_fixedOrder

/-- Shared diagonal limit together with two different fixed-order collision scales. -/
def statement (D : pom_diagonal_observation_strong_unidentifiability_data) : Prop :=
  Tendsto (pomDiagonalQuadraticFreeEnergy
      D.pom_diagonal_observation_strong_unidentifiability_leftPartitionSum)
    atTop
    (nhds
      (D.pom_diagonal_observation_strong_unidentifiability_tau *
        D.pom_diagonal_observation_strong_unidentifiability_alphaStar)) ∧
  Tendsto (pomDiagonalQuadraticFreeEnergy
      D.pom_diagonal_observation_strong_unidentifiability_rightPartitionSum)
    atTop
    (nhds
      (D.pom_diagonal_observation_strong_unidentifiability_tau *
        D.pom_diagonal_observation_strong_unidentifiability_alphaStar)) ∧
  D.pom_diagonal_observation_strong_unidentifiability_concentratedScale ≠
    D.pom_diagonal_observation_strong_unidentifiability_diffuseScale

end pom_diagonal_observation_strong_unidentifiability_data

/-- Paper label: `cor:pom-diagonal-observation-strong-unidentifiability`. -/
theorem paper_pom_diagonal_observation_strong_unidentifiability
    (D : pom_diagonal_observation_strong_unidentifiability_data) : D.statement := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [
      pom_diagonal_observation_strong_unidentifiability_data.statement,
      pom_diagonal_observation_strong_unidentifiability_data.pom_diagonal_observation_strong_unidentifiability_leftData
    ] using
      paper_pom_diagonal_moment_free_energy_degeneracy
        (D.pom_diagonal_observation_strong_unidentifiability_leftData)
  · simpa [
      pom_diagonal_observation_strong_unidentifiability_data.statement,
      pom_diagonal_observation_strong_unidentifiability_data.pom_diagonal_observation_strong_unidentifiability_rightData
    ] using
      paper_pom_diagonal_moment_free_energy_degeneracy
        (D.pom_diagonal_observation_strong_unidentifiability_rightData)
  · simpa [
      pom_diagonal_observation_strong_unidentifiability_data.pom_diagonal_observation_strong_unidentifiability_concentratedScale,
      pom_diagonal_observation_strong_unidentifiability_data.pom_diagonal_observation_strong_unidentifiability_diffuseScale
    ] using
      D.pom_diagonal_observation_strong_unidentifiability_collisionScale_separated

end Omega.POM
