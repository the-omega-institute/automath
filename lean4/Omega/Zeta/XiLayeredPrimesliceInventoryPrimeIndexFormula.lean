import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Folding.KilloLayeredPrimeSlicesFiniteDepth
import Omega.POM.CoprimeLedgerPrimorialOptimality
import Omega.Zeta.LayeredPrimesliceLocalAlphabetFibermax

namespace Omega.Zeta

private def xi_layered_primeslice_inventory_prime_index_formula_constMap (B : ℕ) :
    Fin B → PUnit := fun _ => PUnit.unit

private def xi_layered_primeslice_inventory_prime_index_formula_fiberEquiv (B : ℕ) :
    LayerFiber (xi_layered_primeslice_inventory_prime_index_formula_constMap B) PUnit.unit ≃
      Fin B where
  toFun x := x.1
  invFun i := ⟨i, rfl⟩
  left_inv x := by
    cases x
    rfl
  right_inv i := by
    rfl

private lemma xi_layered_primeslice_inventory_prime_index_formula_fiber_card (B : ℕ) :
    Nat.card
        (LayerFiber (xi_layered_primeslice_inventory_prime_index_formula_constMap B) PUnit.unit) =
      B := by
  simpa using Nat.card_congr
    (xi_layered_primeslice_inventory_prime_index_formula_fiberEquiv B)

/-- Paper label: `cor:xi-layered-primeslice-inventory-prime-index-formula`.
The first `B` labels in the `j`-th prime slice already give a locally invertible alphabet of size
`B`; their indices are the odd numbers with `2`-adic valuation `j`, so the prime labels are
pairwise distinct, the last retained prime has index `2^j(2B-1)`, and the ambient nth-prime
growth bound supplies the explicit lower growth estimate. -/
theorem paper_xi_layered_primeslice_inventory_prime_index_formula (j B : ℕ) :
    (∃ q : Fin B → Fin B,
      FiberwiseInjective (xi_layered_primeslice_inventory_prime_index_formula_constMap B) q) ∧
      Function.Injective (fun i : Fin B => Omega.Folding.layeredPrime j i.1) ∧
      (Finset.univ.image (fun i : Fin B => Omega.Folding.layeredPrime j i.1)).card = B ∧
      (∀ i : Fin B,
        Omega.Folding.layeredPrime j i.1 = Omega.Folding.nthPrime (2 ^ j * (2 * i.1 + 1))) ∧
      (∀ _ : 0 < B,
        Omega.Folding.layeredPrime j (B - 1) = Omega.Folding.nthPrime (2 ^ j * (2 * B - 1))) ∧
      (2 ^ j * (2 * B + 1) + 2 ≤ Omega.Folding.layeredPrime j B) := by
  have hmax :
      ∀ y, Nat.card (LayerFiber (xi_layered_primeslice_inventory_prime_index_formula_constMap B) y)
        ≤ B := by
    intro y
    cases y
    exact le_of_eq (xi_layered_primeslice_inventory_prime_index_formula_fiber_card B)
  have hwit :
      ∃ y,
        Nat.card (LayerFiber (xi_layered_primeslice_inventory_prime_index_formula_constMap B) y) =
          B := by
    exact ⟨PUnit.unit, xi_layered_primeslice_inventory_prime_index_formula_fiber_card B⟩
  have hlocal :
      (∃ q : Fin B → Fin B,
        FiberwiseInjective (xi_layered_primeslice_inventory_prime_index_formula_constMap B) q) := by
    exact
      (paper_xi_layered_primeslice_local_alphabet_fibermax
        (X := Fin B) (Y := PUnit) (Λ := Fin B)
        (xi_layered_primeslice_inventory_prime_index_formula_constMap B) B hmax hwit).2
        (by simp)
  have hinj :
      Function.Injective (fun i : Fin B => Omega.Folding.layeredPrime j i.1) := by
    intro i i' h
    exact Fin.ext (Omega.Folding.layeredPrime_injective h).2
  have hcard :
      (Finset.univ.image (fun i : Fin B => Omega.Folding.layeredPrime j i.1)).card = B := by
    classical
    simpa using
      Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin B)))
        (f := fun i : Fin B => Omega.Folding.layeredPrime j i.1) hinj
  refine ⟨hlocal, hinj, hcard, ?_, ?_, ?_⟩
  · intro i
    simp [Omega.Folding.layeredPrime, Omega.Folding.primeSliceIndex]
  · intro hB
    have hodd : 2 * (B - 1) + 1 = 2 * B - 1 := by
      omega
    have hindex : 2 ^ j * (2 * (B - 1) + 1) = 2 ^ j * (2 * B - 1) := by
      rw [hodd]
    rw [Omega.Folding.layeredPrime, Omega.Folding.primeSliceIndex, hindex]
  · simpa [Omega.Folding.layeredPrime, Omega.Folding.primeSliceIndex] using
      Nat.add_two_le_nth_prime (2 ^ j * (2 * B + 1))

end Omega.Zeta
