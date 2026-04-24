import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete arithmetic package for the intermediate quotient node-count law at the tame collision
primes. The arithmetic genus follows the Hurwitz/Burnside count, the node count removes the six
nodes fixed by each transposition in the quotient, and the normalized genus is obtained by
subtracting the node count from the arithmetic genus. -/
structure XiTerminalZmDeltaS5IntermediateQuotientCollisionData where
  subgroupOrder : ℕ
  fiveCycleCount : ℕ
  transpositionCount : ℕ
  arithmeticGenus : ℕ
  nodeCount : ℕ
  normalizedGenus : ℕ
  subgroupOrder_pos : 0 < subgroupOrder
  transposition_bound : 6 * transpositionCount ≤ 60
  quotient_genus_bound : 2 * fiveCycleCount + 12 * transpositionCount ≤ 48
  arithmeticNumerator_split :
    108 - 2 * fiveCycleCount - 18 * transpositionCount =
      (60 - 6 * transpositionCount) + (48 - 2 * fiveCycleCount - 12 * transpositionCount)
  nodeNumerator_dvd : subgroupOrder ∣ 60 - 6 * transpositionCount
  normalizedNumerator_dvd : subgroupOrder ∣ 48 - 2 * fiveCycleCount - 12 * transpositionCount
  arithmeticGenus_eq :
    arithmeticGenus =
      1 + (108 - 2 * fiveCycleCount - 18 * transpositionCount) / subgroupOrder
  nodeCount_eq : nodeCount = (60 - 6 * transpositionCount) / subgroupOrder
  normalizedGenus_eq : normalizedGenus = arithmeticGenus - nodeCount

/-- Paper label: `thm:xi-terminal-zm-delta-s5-intermediate-quotient-collision-nodal-count`. -/
theorem paper_xi_terminal_zm_delta_s5_intermediate_quotient_collision_nodal_count
    (D : XiTerminalZmDeltaS5IntermediateQuotientCollisionData) :
    D.nodeCount = (60 - 6 * D.transpositionCount) / D.subgroupOrder ∧
      D.normalizedGenus =
        1 + (48 - 2 * D.fiveCycleCount - 12 * D.transpositionCount) / D.subgroupOrder := by
  rcases D.nodeNumerator_dvd with ⟨u, hu⟩
  rcases D.normalizedNumerator_dvd with ⟨v, hv⟩
  have hnodeDiv : (60 - 6 * D.transpositionCount) / D.subgroupOrder = u := by
    exact Nat.div_eq_of_eq_mul_right D.subgroupOrder_pos hu
  have hnormDiv :
      (48 - 2 * D.fiveCycleCount - 12 * D.transpositionCount) / D.subgroupOrder = v := by
    exact Nat.div_eq_of_eq_mul_right D.subgroupOrder_pos hv
  have harithDiv :
      (108 - 2 * D.fiveCycleCount - 18 * D.transpositionCount) / D.subgroupOrder = u + v := by
    have hsum :
        108 - 2 * D.fiveCycleCount - 18 * D.transpositionCount =
          D.subgroupOrder * (u + v) := by
      calc
        108 - 2 * D.fiveCycleCount - 18 * D.transpositionCount =
            (60 - 6 * D.transpositionCount) +
              (48 - 2 * D.fiveCycleCount - 12 * D.transpositionCount) :=
          D.arithmeticNumerator_split
        _ = D.subgroupOrder * u + D.subgroupOrder * v := by rw [hu, hv]
        _ = D.subgroupOrder * (u + v) := by ring
    exact Nat.div_eq_of_eq_mul_right D.subgroupOrder_pos hsum
  constructor
  · exact D.nodeCount_eq
  · calc
      D.normalizedGenus = D.arithmeticGenus - D.nodeCount := D.normalizedGenus_eq
      _ = (1 + (u + v)) - u := by rw [D.arithmeticGenus_eq, D.nodeCount_eq, harithDiv, hnodeDiv]
      _ = 1 + v := by omega
      _ = 1 + (48 - 2 * D.fiveCycleCount - 12 * D.transpositionCount) / D.subgroupOrder := by
        rw [hnormDiv]

end Omega.Zeta
