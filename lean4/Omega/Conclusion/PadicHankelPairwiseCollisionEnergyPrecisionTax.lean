import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite valuation data for the Hankel precision tax.  The determinant valuation is
recorded through the dominant-chain product expansion, and the adjugate numerator valuations record
the valuation-ring integrality of `adj(H) b`. -/
structure conclusion_padic_hankel_pairwise_collision_energy_precision_tax_data where
  conclusion_padic_hankel_pairwise_collision_energy_precision_tax_r : ℕ
  conclusion_padic_hankel_pairwise_collision_energy_precision_tax_collision_val :
    Fin (conclusion_padic_hankel_pairwise_collision_energy_precision_tax_r + 1) →
      Fin (conclusion_padic_hankel_pairwise_collision_energy_precision_tax_r + 1) → ℤ
  conclusion_padic_hankel_pairwise_collision_energy_precision_tax_adjugate_numerator_val :
    Fin (conclusion_padic_hankel_pairwise_collision_energy_precision_tax_r + 1) → ℤ
  conclusion_padic_hankel_pairwise_collision_energy_precision_tax_adjugate_numerator_integral :
    ∀ i,
      0 ≤
        conclusion_padic_hankel_pairwise_collision_energy_precision_tax_adjugate_numerator_val i

namespace conclusion_padic_hankel_pairwise_collision_energy_precision_tax_data

/-- Valuation of the product of collisions contributed when the new node `j` enters the dominant
chain. -/
def conclusion_padic_hankel_pairwise_collision_energy_precision_tax_product_val
    (D : conclusion_padic_hankel_pairwise_collision_energy_precision_tax_data)
    (j : Fin (D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_r + 1)) : ℤ :=
  (Finset.univ.filter (fun i :
      Fin (D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_r + 1) =>
      i.val < j.val)).sum
    (fun i => D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_collision_val i j)

/-- Determinant valuation supplied by the nonarchimedean dominant-chain product formula. -/
def conclusion_padic_hankel_pairwise_collision_energy_precision_tax_det_val
    (D : conclusion_padic_hankel_pairwise_collision_energy_precision_tax_data) : ℤ :=
  2 *
    ∑ j : Fin (D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_r + 1),
      D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_product_val j

/-- Pairwise collision energy, indexed as the finite double sum over ordered pairs `i < j`. -/
def conclusion_padic_hankel_pairwise_collision_energy_precision_tax_pairwise_energy
    (D : conclusion_padic_hankel_pairwise_collision_energy_precision_tax_data) : ℤ :=
  2 *
    (Finset.univ.sigma (fun j :
      Fin (D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_r + 1) =>
      Finset.univ.filter (fun i :
        Fin (D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_r + 1) =>
        i.val < j.val))).sum
      (fun ij =>
        D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_collision_val ij.2 ij.1)

/-- Coordinate valuation of the adjugate-form solution `x = adj(H)b / det(H)`. -/
def conclusion_padic_hankel_pairwise_collision_energy_precision_tax_solution_val
    (D : conclusion_padic_hankel_pairwise_collision_energy_precision_tax_data)
    (i : Fin (D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_r + 1)) : ℤ :=
  D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_adjugate_numerator_val i -
    D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_det_val

/-- The finite precision-tax containment: every adjugate solution coordinate lies in
`π^{-s_r} O`. -/
def conclusion_padic_hankel_pairwise_collision_energy_precision_tax_containment
    (D : conclusion_padic_hankel_pairwise_collision_energy_precision_tax_data) : Prop :=
  ∀ i : Fin (D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_r + 1),
    -D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_det_val ≤
      D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_solution_val i

/-- The paper-facing finite statement: the dominant-chain determinant valuation is the pairwise
collision energy and the adjugate formula gives the corresponding precision containment. -/
def conclusion_padic_hankel_pairwise_collision_energy_precision_tax_statement
    (D : conclusion_padic_hankel_pairwise_collision_energy_precision_tax_data) : Prop :=
  D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_det_val =
      D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_pairwise_energy ∧
    D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_containment

end conclusion_padic_hankel_pairwise_collision_energy_precision_tax_data

open conclusion_padic_hankel_pairwise_collision_energy_precision_tax_data

/-- Paper label: `thm:conclusion-padic-hankel-pairwise-collision-energy-precision-tax`. -/
theorem paper_conclusion_padic_hankel_pairwise_collision_energy_precision_tax
    (D : conclusion_padic_hankel_pairwise_collision_energy_precision_tax_data) :
    conclusion_padic_hankel_pairwise_collision_energy_precision_tax_statement D := by
  constructor
  · simp [conclusion_padic_hankel_pairwise_collision_energy_precision_tax_det_val,
      conclusion_padic_hankel_pairwise_collision_energy_precision_tax_pairwise_energy,
      conclusion_padic_hankel_pairwise_collision_energy_precision_tax_product_val,
      Finset.sum_sigma]
  · intro i
    rw [conclusion_padic_hankel_pairwise_collision_energy_precision_tax_solution_val]
    have hintegral :=
      D.conclusion_padic_hankel_pairwise_collision_energy_precision_tax_adjugate_numerator_integral
        i
    linarith

end Omega.Conclusion
