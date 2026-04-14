import Mathlib

namespace Omega.Conclusion.CofinalFixedQuotient

theorem paper_conclusion_cofinal_fixed_quotient_seeds
    {H Q : Type} [Fintype H] [Fintype Q] (π : H → Q) (hπ : Function.Surjective π) :
    Fintype.card Q ≤ Fintype.card H :=
  Fintype.card_le_of_surjective π hπ

theorem paper_conclusion_cofinal_fixed_quotient_package
    {H Q : Type} [Fintype H] [Fintype Q] (π : H → Q) (hπ : Function.Surjective π) :
    Fintype.card Q ≤ Fintype.card H :=
  paper_conclusion_cofinal_fixed_quotient_seeds π hπ

end Omega.Conclusion.CofinalFixedQuotient
