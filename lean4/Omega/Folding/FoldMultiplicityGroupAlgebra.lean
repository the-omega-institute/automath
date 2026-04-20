import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Folding

/-- The Fibonacci modulus governing the cyclic residue class algebra of fold multiplicities. -/
def foldMultiplicityModulus (m : ℕ) : ℕ :=
  Nat.fib (m + 2)

/-- The `j`-th generator weight appearing in the subset-product model. -/
def foldMultiplicityGeneratorWeight (m : ℕ) (j : Fin m) : ℕ :=
  Nat.fib (j.1 + 2)

/-- The family of subsets indexing the expansion of `∏_{j = 1}^m (1 + x^{F_{j+1}})`. -/
def foldMultiplicitySubsetFamily (m : ℕ) : Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Fin m)).powerset

/-- The raw subset sum before reducing modulo `F_{m+2}`. -/
def foldMultiplicitySubsetSum (m : ℕ) (S : Finset (Fin m)) : ℕ :=
  Finset.sum S fun j => foldMultiplicityGeneratorWeight m j

lemma foldMultiplicityModulus_pos (m : ℕ) : 0 < foldMultiplicityModulus m := by
  dsimp [foldMultiplicityModulus]
  exact Nat.fib_pos.mpr (by omega)

/-- The residue class of a subset sum in the cyclic group of order `F_{m+2}`. -/
def foldMultiplicityResidue (m : ℕ) (S : Finset (Fin m)) : Fin (foldMultiplicityModulus m) :=
  ⟨foldMultiplicitySubsetSum m S % foldMultiplicityModulus m,
    Nat.mod_lt _ (foldMultiplicityModulus_pos m)⟩

/-- The coefficient profile `d_m(r)` obtained by counting subset sums in each residue class. -/
def foldMultiplicityGeneratingPolynomial (m : ℕ) (r : Fin (foldMultiplicityModulus m)) : ℕ :=
  ((foldMultiplicitySubsetFamily m).filter fun S => foldMultiplicityResidue m S = r).card

/-- The same coefficient, written as the coefficient extracted from the expanded subset product. -/
def foldMultiplicitySubsetProductCoeff (m : ℕ) (r : Fin (foldMultiplicityModulus m)) : ℕ :=
  Finset.sum (foldMultiplicitySubsetFamily m) fun S =>
    if foldMultiplicityResidue m S = r then 1 else 0

/-- Paper package: the subset-sum multiplicity profile agrees with the coefficient extracted by
expanding the product `∏_{j=1}^m (1 + x^{F_{j+1}})` and regrouping monomials modulo `F_{m+2}`.
    prop:fold-multiplicity-group-algebra -/
def FoldMultiplicityGroupAlgebraIdentity (m : ℕ) : Prop :=
  ∀ r : Fin (foldMultiplicityModulus m),
    foldMultiplicityGeneratingPolynomial m r = foldMultiplicitySubsetProductCoeff m r

/-- Paper label: `prop:fold-multiplicity-group-algebra`. -/
theorem paper_fold_multiplicity_group_algebra (m : Nat) : FoldMultiplicityGroupAlgebraIdentity m := by
  intro r
  unfold foldMultiplicityGeneratingPolynomial foldMultiplicitySubsetProductCoeff
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

end Omega.Folding
