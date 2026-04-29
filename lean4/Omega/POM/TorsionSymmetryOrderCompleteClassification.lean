import Mathlib.Tactic

namespace Omega.POM

/-- Concrete support data for the torsion-order classification theorem. The support gcd is
characterized by the usual universal divisibility property on the finite support. -/
structure TorsionSymmetryOrderCompleteClassificationData where
  support : Finset ℕ
  supportGcd : ℕ
  pom_torsion_symmetry_order_complete_classification_support_gcd_dvd :
    ∀ n ∈ support, supportGcd ∣ n
  pom_torsion_symmetry_order_complete_classification_support_gcd_greatest :
    ∀ q : ℕ, (∀ n ∈ support, q ∣ n) → q ∣ supportGcd

namespace TorsionSymmetryOrderCompleteClassificationData

/-- The support is nonempty exactly when the underlying finite set is nonempty. -/
def supportNonempty (D : TorsionSymmetryOrderCompleteClassificationData) : Prop :=
  D.support.Nonempty

/-- Admissible torsion orders are exactly the integers `q ≥ 2` dividing every support index. -/
def torsionOrders (D : TorsionSymmetryOrderCompleteClassificationData) : Set ℕ :=
  {q : ℕ | 2 ≤ q ∧ ∀ n ∈ D.support, q ∣ n}

end TorsionSymmetryOrderCompleteClassificationData

open TorsionSymmetryOrderCompleteClassificationData

/-- Paper label: `thm:pom-torsion-symmetry-order-complete-classification`. Once the support gcd is
packaged concretely, the admissible torsion orders are exactly its divisors in the nonempty case,
while the empty-support case is vacuous. -/
theorem paper_pom_torsion_symmetry_order_complete_classification
    (D : TorsionSymmetryOrderCompleteClassificationData) :
    (D.supportNonempty → D.torsionOrders = {q : ℕ | 2 ≤ q ∧ q ∣ D.supportGcd}) ∧
      (¬ D.supportNonempty → D.torsionOrders = {q : ℕ | 2 ≤ q}) := by
  constructor
  · intro _
    ext q
    constructor
    · intro hq
      exact ⟨hq.1,
        D.pom_torsion_symmetry_order_complete_classification_support_gcd_greatest q hq.2⟩
    · intro hq
      refine ⟨hq.1, ?_⟩
      intro n hn
      exact dvd_trans hq.2
        (D.pom_torsion_symmetry_order_complete_classification_support_gcd_dvd n hn)
  · intro hEmpty
    ext q
    constructor
    · intro hq
      exact hq.1
    · intro hq
      refine ⟨hq, ?_⟩
      intro n hn
      exact False.elim (hEmpty ⟨n, hn⟩)

end Omega.POM
