import Mathlib.Data.Fintype.Basic
import Omega.Zeta.XiLayeredPrimesliceInventoryPrimeIndexFormula

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Concrete finite inventory for the dyadic-head prime-slice law. -/
structure conclusion_layered_primeslice_dyadic_head_law_data where
  k : ℕ
  B : Fin k → ℕ

/-- The lexicographically minimal inventory is obtained by taking the first `B j` primes in each
dyadic slice.  Its labels are globally distinct, its total cardinality is the sum of the layer
sizes, and every layer has the advertised top-prime index. -/
def conclusion_layered_primeslice_dyadic_head_law_statement
    (D : conclusion_layered_primeslice_dyadic_head_law_data) : Prop :=
  (∀ j : Fin D.k,
    Function.Injective (fun i : Fin (D.B j) => Omega.Folding.layeredPrime j.1 i.1) ∧
      (Finset.univ.image
        (fun i : Fin (D.B j) => Omega.Folding.layeredPrime j.1 i.1)).card = D.B j ∧
      (∀ i : Fin (D.B j),
        Omega.Folding.layeredPrime j.1 i.1 =
          Omega.Folding.nthPrime (2 ^ j.1 * (2 * i.1 + 1))) ∧
      (∀ _ : 0 < D.B j,
        Omega.Folding.layeredPrime j.1 (D.B j - 1) =
          Omega.Folding.nthPrime (2 ^ j.1 * (2 * D.B j - 1)))) ∧
    Function.Injective
      (fun x : Σ j : Fin D.k, Fin (D.B j) => Omega.Folding.layeredPrime x.1.1 x.2.1) ∧
    (Finset.univ.image
      (fun x : Σ j : Fin D.k, Fin (D.B j) =>
        Omega.Folding.layeredPrime x.1.1 x.2.1)).card =
      ∑ j : Fin D.k, D.B j

/-- Paper label: `thm:conclusion-layered-primeslice-dyadic-head-law`. -/
theorem paper_conclusion_layered_primeslice_dyadic_head_law
    (D : conclusion_layered_primeslice_dyadic_head_law_data) :
    conclusion_layered_primeslice_dyadic_head_law_statement D := by
  classical
  have hlayers :
      ∀ j : Fin D.k,
        Function.Injective (fun i : Fin (D.B j) => Omega.Folding.layeredPrime j.1 i.1) ∧
          (Finset.univ.image
            (fun i : Fin (D.B j) => Omega.Folding.layeredPrime j.1 i.1)).card = D.B j ∧
          (∀ i : Fin (D.B j),
            Omega.Folding.layeredPrime j.1 i.1 =
              Omega.Folding.nthPrime (2 ^ j.1 * (2 * i.1 + 1))) ∧
          (∀ _ : 0 < D.B j,
            Omega.Folding.layeredPrime j.1 (D.B j - 1) =
              Omega.Folding.nthPrime (2 ^ j.1 * (2 * D.B j - 1))) := by
    intro j
    rcases Omega.Zeta.paper_xi_layered_primeslice_inventory_prime_index_formula.{0} j.1 (D.B j)
      with ⟨_, hinj, hcard, hformula, htop, _⟩
    exact ⟨hinj, hcard, hformula, htop⟩
  have hglobal_inj :
      Function.Injective
        (fun x : Σ j : Fin D.k, Fin (D.B j) =>
          Omega.Folding.layeredPrime x.1.1 x.2.1) := by
    intro x y hxy
    rcases Omega.Folding.layeredPrime_injective hxy with ⟨hlevel, hcoord⟩
    cases x with
    | mk j i =>
      cases y with
      | mk j' i' =>
        simp only at hlevel hcoord
        have hj : j = j' := Fin.ext hlevel
        subst j'
        have hi : i = i' := Fin.ext hcoord
        cases hi
        rfl
  have hdomain_card :
      Fintype.card (Σ j : Fin D.k, Fin (D.B j)) = ∑ j : Fin D.k, D.B j := by
    simp
  have hglobal_card :
      (Finset.univ.image
        (fun x : Σ j : Fin D.k, Fin (D.B j) =>
          Omega.Folding.layeredPrime x.1.1 x.2.1)).card =
        ∑ j : Fin D.k, D.B j := by
    rw [Finset.card_image_of_injective _ hglobal_inj]
    simp [hdomain_card]
  exact ⟨hlayers, hglobal_inj, hglobal_card⟩

end

end Omega.Conclusion
