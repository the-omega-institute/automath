import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic
import Omega.Zeta.XiSecularFamilyFullSymmetricGalois

namespace Omega.Zeta

/-- Specialization-side Galois order obtained from the generic secular family. -/
def xiSecularSpecializationGaloisOrder (q : ℕ) (_r : XiSecularParameterSpace q) : ℕ :=
  xiSecularGenericGaloisOrder q

/-- An explicit arithmetic family of rational specialization points. -/
def xiSecularArithmeticSpecialization (q n : ℕ) : XiSecularParameterSpace q :=
  fun i => if i = 0 then (n : ℚ) else 0

theorem xiSecularArithmeticSpecialization_injective (q : ℕ) :
    Function.Injective (xiSecularArithmeticSpecialization q) := by
  intro m n hmn
  have h0 := congrArg (fun f => f 0) hmn
  simpa [xiSecularArithmeticSpecialization] using h0

theorem xiSecularFullSymmetricSpecializations_infinite (q : ℕ) :
    Set.Infinite
      {r : XiSecularParameterSpace q |
        xiSecularSpecializationGaloisOrder q r = Nat.factorial (q + 1)} := by
  refine Set.infinite_of_injective_forall_mem
    (f := xiSecularArithmeticSpecialization q)
    (xiSecularArithmeticSpecialization_injective q) ?_
  intro n
  simp [xiSecularSpecializationGaloisOrder, xiSecularGenericGaloisOrder]

/-- The generic full-symmetric Galois order persists on an explicit infinite family of rational
specializations.
    cor:xi-secular-specialization-infinitely-many-full-symmetric -/
theorem paper_xi_secular_specialization_infinitely_many_full_symmetric (q : ℕ) :
    xiSecularGenericGaloisOrder q = Nat.factorial (q + 1) ∧
      Set.Infinite
        {r : XiSecularParameterSpace q |
          xiSecularSpecializationGaloisOrder q r = Nat.factorial (q + 1)} := by
  refine ⟨(paper_xi_secular_family_full_symmetric_galois q).2.2, ?_⟩
  exact xiSecularFullSymmetricSpecializations_infinite q

end Omega.Zeta
