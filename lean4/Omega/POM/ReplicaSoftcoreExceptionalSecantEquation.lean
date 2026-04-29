import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Data for the exceptional block after passing to the `S_q`-symmetric eigenbasis.
The field `resolventWitness` is the rank-one determinant/resolvent identity written at the
exceptional eigenvalue `rho`. -/
structure ReplicaSoftcoreExceptionalSecantData where
  q : ℕ
  hq : 2 ≤ q
  rho : ℝ
  node : Fin (q + 1) → ℝ
  weight : Fin (q + 1) → ℝ
  node_lt_rho : ∀ i, node i < rho
  resolventWitness :
    1 - (1 / 2 : ℝ) * ∑ i : Fin (q + 1), weight i / (rho - node i) = 0

/-- The rank-one resolvent identity on the exceptional block rearranges to the secant equation
for the Perron root, and the strict inequalities `d_i < rho` keep every pole off the summation
contour.
    prop:pom-replica-softcore-exceptional-secant-equation -/
theorem paper_pom_replica_softcore_exceptional_secant_equation
    (D : ReplicaSoftcoreExceptionalSecantData) :
    (∑ i : Fin (D.q + 1), D.weight i / (D.rho - D.node i) = 2) ∧
      (∀ i : Fin (D.q + 1), 0 < D.rho - D.node i) := by
  refine ⟨?_, ?_⟩
  · linarith [D.resolventWitness]
  · intro i
    linarith [D.node_lt_rho i]

/-- cor:pom-replica-softcore-secant-equation-expectation-form -/
theorem paper_pom_replica_softcore_secant_equation_expectation_form
    (D : ReplicaSoftcoreExceptionalSecantData) :
    (∑ i : Fin (D.q + 1), (D.weight i / (2 : ℝ) ^ D.q) / (D.rho - D.node i)) =
      2 / (2 : ℝ) ^ D.q := by
  have hsecant := (paper_pom_replica_softcore_exceptional_secant_equation D).1
  have hpoles := (paper_pom_replica_softcore_exceptional_secant_equation D).2
  calc
    (∑ i : Fin (D.q + 1), (D.weight i / (2 : ℝ) ^ D.q) / (D.rho - D.node i)) =
        ∑ i : Fin (D.q + 1),
          (D.weight i / (D.rho - D.node i)) / (2 : ℝ) ^ D.q := by
      refine Finset.sum_congr rfl ?_
      intro i _
      have hpow : (2 : ℝ) ^ D.q ≠ 0 := by positivity
      have hpole : D.rho - D.node i ≠ 0 := ne_of_gt (hpoles i)
      field_simp [hpow, hpole]
    _ = (∑ i : Fin (D.q + 1), D.weight i / (D.rho - D.node i)) /
        (2 : ℝ) ^ D.q := by
      rw [Finset.sum_div]
    _ = 2 / (2 : ℝ) ^ D.q := by
      rw [hsecant]

end Omega.POM
