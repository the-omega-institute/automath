import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Atom-level data for a squarefree Boolean gcd/lcm arithmeticization.

The base value is the value at the empty face, each coordinate is read from the singleton
atom, and the last field says that adjoining a new coordinate is computed by `lcm`. -/
def xi_chain_interior_squarefree_gcd_lcm_normalform_admissible
    (n : ℕ) (η : Finset (Fin n) → ℕ) : Prop :=
  ∃ b : ℕ, ∃ r : Fin n → ℕ,
    η ∅ = b ∧
      Squarefree b ∧
      (∀ i : Fin n, 1 < r i ∧ Squarefree (r i) ∧ Nat.Coprime b (r i)) ∧
      (∀ i j : Fin n, i ≠ j → Nat.Coprime (r i) (r j)) ∧
      (∀ i : Fin n, η {i} = b * r i) ∧
      (∀ (S : Finset (Fin n)) (i : Fin n), i ∉ S →
        η (insert i S) = Nat.lcm (η S) (η {i}))

/-- Product normal form for a squarefree Boolean gcd/lcm arithmeticization. -/
def xi_chain_interior_squarefree_gcd_lcm_normalform_conclusion
    (n : ℕ) (η : Finset (Fin n) → ℕ) : Prop :=
  ∃ b : ℕ, ∃ r : Fin n → ℕ,
    η ∅ = b ∧
      Squarefree b ∧
      (∀ i : Fin n, 1 < r i ∧ Squarefree (r i) ∧ Nat.Coprime b (r i)) ∧
      (∀ i j : Fin n, i ≠ j → Nat.Coprime (r i) (r j)) ∧
      (∀ S : Finset (Fin n), η S = b * ∏ i ∈ S, r i)

lemma xi_chain_interior_squarefree_gcd_lcm_normalform_base_coprime
    {n : ℕ} {b : ℕ} {r : Fin n → ℕ}
    (hb : ∀ i : Fin n, Nat.Coprime b (r i)) (S : Finset (Fin n)) :
    Nat.Coprime b (∏ i ∈ S, r i) := by
  exact Nat.Coprime.prod_right fun i _hi => hb i

lemma xi_chain_interior_squarefree_gcd_lcm_normalform_prod_coprime
    {n : ℕ} {r : Fin n → ℕ}
    (hr : ∀ i j : Fin n, i ≠ j → Nat.Coprime (r i) (r j))
    {S : Finset (Fin n)} {i : Fin n} (hi : i ∉ S) :
    Nat.Coprime (∏ j ∈ S, r j) (r i) := by
  refine Nat.Coprime.prod_left fun j hj => ?_
  exact hr j i (fun hji => hi (hji ▸ hj))

lemma xi_chain_interior_squarefree_gcd_lcm_normalform_lcm_step
    {n : ℕ} {b : ℕ} {r : Fin n → ℕ}
    (hr : ∀ i j : Fin n, i ≠ j → Nat.Coprime (r i) (r j))
    {S : Finset (Fin n)} {i : Fin n} (hi : i ∉ S) :
    Nat.lcm (b * ∏ j ∈ S, r j) (b * r i) =
      b * ∏ j ∈ insert i S, r j := by
  have hprod : Nat.Coprime (∏ j ∈ S, r j) (r i) :=
    xi_chain_interior_squarefree_gcd_lcm_normalform_prod_coprime hr hi
  calc
    Nat.lcm (b * ∏ j ∈ S, r j) (b * r i)
        = b * Nat.lcm (∏ j ∈ S, r j) (r i) := by
          change lcm (b * ∏ j ∈ S, r j) (b * r i) =
            b * lcm (∏ j ∈ S, r j) (r i)
          rw [lcm_mul_left]
          simp
      _ = b * ((∏ j ∈ S, r j) * r i) := by
          rw [hprod.lcm_eq_mul]
      _ = b * ∏ j ∈ insert i S, r j := by
          rw [Finset.prod_insert hi]
          ring

lemma xi_chain_interior_squarefree_gcd_lcm_normalform_product
    {n : ℕ} {η : Finset (Fin n) → ℕ} {b : ℕ} {r : Fin n → ℕ}
    (hbase : η ∅ = b)
    (hr : ∀ i j : Fin n, i ≠ j → Nat.Coprime (r i) (r j))
    (hatom : ∀ i : Fin n, η {i} = b * r i)
    (hjoin : ∀ (S : Finset (Fin n)) (i : Fin n), i ∉ S →
      η (insert i S) = Nat.lcm (η S) (η {i})) :
    ∀ S : Finset (Fin n), η S = b * ∏ i ∈ S, r i := by
  intro S
  refine S.induction_on ?base ?step
  · simpa using hbase
  · intro i S hi hS
    rw [hjoin S i hi, hS, hatom i]
    exact xi_chain_interior_squarefree_gcd_lcm_normalform_lcm_step hr hi

/-- Paper label: `thm:xi-chain-interior-squarefree-gcd-lcm-normalform`. -/
theorem paper_xi_chain_interior_squarefree_gcd_lcm_normalform
    (n : ℕ) (η : Finset (Fin n) → ℕ)
    (hη : xi_chain_interior_squarefree_gcd_lcm_normalform_admissible n η) :
    xi_chain_interior_squarefree_gcd_lcm_normalform_conclusion n η := by
  rcases hη with ⟨b, r, hbase, hb_sq, hr_data, hr_pairwise, hatom, hjoin⟩
  refine ⟨b, r, hbase, hb_sq, hr_data, hr_pairwise, ?_⟩
  exact xi_chain_interior_squarefree_gcd_lcm_normalform_product hbase
    hr_pairwise hatom hjoin

end Omega.Zeta
