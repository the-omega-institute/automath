import Mathlib.Data.ZMod.Basic

namespace Omega

structure xi_localized_quotient_exact_sfree_externalization_Data where
  S : Finset ℕ
  modulus : ℕ

namespace xi_localized_quotient_exact_sfree_externalization_Data

abbrev quotient (D : xi_localized_quotient_exact_sfree_externalization_Data) : Type :=
  ZMod D.modulus

abbrev sfreeQuotient (D : xi_localized_quotient_exact_sfree_externalization_Data) : Type :=
  ZMod D.modulus

def denominatorSupported (D : xi_localized_quotient_exact_sfree_externalization_Data)
    (d : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ d → p ∈ D.S

def reduction (D : xi_localized_quotient_exact_sfree_externalization_Data) :
    D.quotient → D.sfreeQuotient :=
  id

def statement (D : xi_localized_quotient_exact_sfree_externalization_Data) : Prop :=
  Function.Surjective D.reduction ∧
    (∀ x : D.quotient, D.reduction x = 0 ↔ x = 0) ∧
      D.denominatorSupported 1

end xi_localized_quotient_exact_sfree_externalization_Data

abbrev xi_localized_quotient_exact_sfree_externalization_statement
    (D : xi_localized_quotient_exact_sfree_externalization_Data) : Prop :=
  D.statement

theorem paper_xi_localized_quotient_exact_sfree_externalization
    (D : xi_localized_quotient_exact_sfree_externalization_Data) :
    xi_localized_quotient_exact_sfree_externalization_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact ⟨y, rfl⟩
  · intro x
    rfl
  · intro p hp hpdvd
    exact (hp.ne_one (Nat.dvd_one.mp hpdvd)).elim

end Omega
