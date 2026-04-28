import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Concrete finite Euler-product data for the single-conductor torsion factorization.  The two
local identities identify the primitive torsion factor with its cyclotomic packet and then group
that packet by the gcd class used in the Euler factorization. -/
structure conclusion_single_conductor_torsion_cyclotomic_euler_factorization_data where
  conductor : ℕ
  conductor_pos : 0 < conductor
  torsionFactor : ℕ → ℤ
  cyclotomicPacket : ℕ → ℤ
  eulerPacket : ℕ → ℤ
  hCyclotomicPoint :
    ∀ a ∈ Finset.range conductor, torsionFactor a = cyclotomicPacket a
  hEulerPoint :
    ∀ a ∈ Finset.range conductor, cyclotomicPacket a = eulerPacket (Nat.gcd a conductor)

def conclusion_single_conductor_torsion_cyclotomic_euler_factorization_data.cyclotomicFactorization
  (D : conclusion_single_conductor_torsion_cyclotomic_euler_factorization_data) : Prop :=
  (Finset.range D.conductor).prod D.torsionFactor =
    (Finset.range D.conductor).prod D.cyclotomicPacket

def conclusion_single_conductor_torsion_cyclotomic_euler_factorization_data.eulerFactorization
  (D : conclusion_single_conductor_torsion_cyclotomic_euler_factorization_data) : Prop :=
  (Finset.range D.conductor).prod D.cyclotomicPacket =
    (Finset.range D.conductor).prod fun a => D.eulerPacket (Nat.gcd a D.conductor)

/-- Paper label: `thm:conclusion-single-conductor-torsion-cyclotomic-euler-factorization`. -/
theorem paper_conclusion_single_conductor_torsion_cyclotomic_euler_factorization
    (D : conclusion_single_conductor_torsion_cyclotomic_euler_factorization_data) :
    D.cyclotomicFactorization ∧ D.eulerFactorization := by
  refine ⟨?_, ?_⟩
  · exact Finset.prod_congr rfl D.hCyclotomicPoint
  · exact Finset.prod_congr rfl D.hEulerPoint

end Omega.Conclusion
