import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-collision-resultant-minimality`. -/
theorem paper_conclusion_collision_resultant_minimality {Poly : Type*} (degree : Poly → ℕ)
    (divides : Poly → Poly → Prop) {P R : Poly} {d1 d2 rank1 rank2 rankTensor : ℕ}
    (hdiv : divides P R) (hdegree_le_of_div : divides P R → degree P ≤ degree R)
    (hdegree_lower : d1 * d2 ≤ degree P) (hdegree_R : degree R = d1 * d2)
    (heq_of_div_same_degree : divides P R → degree P = degree R → P = R)
    (hrank1 : rank1 = d1) (hrank2 : rank2 = d2)
    (hrankTensor : rankTensor = degree P) :
    P = R ∧ rankTensor = rank1 * rank2 := by
  have hdegree_le : degree P ≤ degree R := hdegree_le_of_div hdiv
  have hdegree_ge : degree R ≤ degree P := by
    calc
      degree R = d1 * d2 := hdegree_R
      _ ≤ degree P := hdegree_lower
  have hdegree_eq : degree P = degree R := Nat.le_antisymm hdegree_le hdegree_ge
  refine ⟨heq_of_div_same_degree hdiv hdegree_eq, ?_⟩
  calc
    rankTensor = degree P := hrankTensor
    _ = degree R := hdegree_eq
    _ = d1 * d2 := hdegree_R
    _ = rank1 * rank2 := by rw [hrank1, hrank2]

end Omega.Conclusion
