import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The squarefree Gödel code attached to a Boolean fixed set. -/
def xi_chain_interior_godel_euler_mobius_factorization_code
    {n : Nat} (q : Fin n → Nat) (S : Finset (Fin n)) : Nat :=
  ∏ i ∈ S, q i

/-- The enumerated squarefree image of the Boolean fixed-set model. -/
def xi_chain_interior_godel_euler_mobius_factorization_image
    {n : Nat} (q : Fin n → Nat) : Finset Nat :=
  (Finset.univ : Finset (Finset (Fin n))).image
    (xi_chain_interior_godel_euler_mobius_factorization_code q)

lemma xi_chain_interior_godel_euler_mobius_factorization_squarefree_product
    {n : Nat} (q : Fin n → Nat) :
    ∀ S : Finset (Fin n),
      (∀ i ∈ S, Squarefree (q i)) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (q i) (q j)) →
      Squarefree (xi_chain_interior_godel_euler_mobius_factorization_code q S) := by
  intro S
  refine S.induction_on ?base ?step
  · intro _ _
    simp [xi_chain_interior_godel_euler_mobius_factorization_code]
  · intro a S ha ih hsq hcop
    have hqa : Squarefree (q a) := hsq a (by simp)
    have hprod :
        Squarefree (xi_chain_interior_godel_euler_mobius_factorization_code q S) := by
      refine ih ?_ ?_
      · intro i hi
        exact hsq i (by simp [hi])
      · intro i hi j hj hij
        exact hcop i (by simp [hi]) j (by simp [hj]) hij
    have hcop_prod :
        Nat.Coprime (q a) (xi_chain_interior_godel_euler_mobius_factorization_code q S) := by
      unfold xi_chain_interior_godel_euler_mobius_factorization_code
      exact Nat.Coprime.prod_right fun i hi =>
        hcop a (by simp) i (by simp [hi]) (fun hai => ha (hai ▸ hi))
    rw [xi_chain_interior_godel_euler_mobius_factorization_code, Finset.prod_insert ha]
    exact (Nat.squarefree_mul hcop_prod).2 ⟨hqa, hprod⟩

/-- Concrete statement package for the Boolean fixed-set Gödel/Euler/Möbius factorization. -/
def xi_chain_interior_godel_euler_mobius_factorization_statement
    (n : Nat) (q : Fin n → Nat) : Prop :=
  (∀ a : Nat,
      a ∈ xi_chain_interior_godel_euler_mobius_factorization_image q ↔
        ∃ S : Finset (Fin n),
          a = xi_chain_interior_godel_euler_mobius_factorization_code q S) ∧
    (∀ S : Finset (Fin n),
      (∀ i ∈ S, Squarefree (q i)) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (q i) (q j)) →
      Squarefree (xi_chain_interior_godel_euler_mobius_factorization_code q S)) ∧
    (∑ S : Finset (Fin n),
        (xi_chain_interior_godel_euler_mobius_factorization_code q S : Int) =
      ∏ i : Fin n, (1 + (q i : Int))) ∧
    (∑ S : Finset (Fin n),
        (-1 : Int) ^ S.card *
          (xi_chain_interior_godel_euler_mobius_factorization_code q S : Int) =
      ∏ i : Fin n, (1 - (q i : Int)))

/-- Paper label: `thm:xi-chain-interior-godel-euler-mobius-factorization`. -/
theorem paper_xi_chain_interior_godel_euler_mobius_factorization
    (n : Nat) (q : Fin n → Nat) :
    xi_chain_interior_godel_euler_mobius_factorization_statement n q := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    rw [xi_chain_interior_godel_euler_mobius_factorization_image, Finset.mem_image]
    constructor
    · intro h
      rcases h with ⟨S, _hS_mem, hS⟩
      exact ⟨S, hS.symm⟩
    · intro h
      rcases h with ⟨S, hS⟩
      exact ⟨S, by simp, hS.symm⟩
  · exact xi_chain_interior_godel_euler_mobius_factorization_squarefree_product q
  · have h :=
      (Finset.prod_one_add
        (s := (Finset.univ : Finset (Fin n))) (f := fun i : Fin n => (q i : Int))).symm
    simpa [xi_chain_interior_godel_euler_mobius_factorization_code] using h
  · have h :=
      (Finset.prod_sub
        (f := fun _ : Fin n => (1 : Int)) (g := fun i : Fin n => (q i : Int))
        (s := (Finset.univ : Finset (Fin n)))).symm
    simpa [xi_chain_interior_godel_euler_mobius_factorization_code, mul_comm, mul_left_comm,
      mul_assoc] using h

end Omega.Zeta
