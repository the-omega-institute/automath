import Omega.Zeta.XiChainInteriorBooleanFlagClosedForm
import Omega.Zeta.XiChainInteriorGodelEulerMobiusFactorization

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete closure statement for the Boolean chain-interior Dirichlet/Möbius package. The two
finite Euler products reuse the Gödel code from the preceding theorem, while the characteristic
identity is the Boolean subset expansion of `(1 - x)^(n - 1)`. -/
def xi_chain_interior_dirichlet_mobius_characteristic_closure_statement
    (n : Nat) (q : Fin n → Nat) : Prop :=
  (∑ S : Finset (Fin n),
      (xi_chain_interior_godel_euler_mobius_factorization_code q S : Int) =
    ∏ i : Fin n, (1 + (q i : Int))) ∧
    (∑ S : Finset (Fin n),
        (-1 : Int) ^ S.card *
          (xi_chain_interior_godel_euler_mobius_factorization_code q S : Int) =
      ∏ i : Fin n, (1 - (q i : Int))) ∧
    (∀ x : Int,
      ∑ S : Finset (Fin (n - 1)), (-1 : Int) ^ S.card * x ^ S.card =
        (1 - x) ^ (n - 1))

/-- Paper label: `cor:xi-chain-interior-dirichlet-mobius-characteristic-closure`. -/
theorem paper_xi_chain_interior_dirichlet_mobius_characteristic_closure
    (n : Nat) (q : Fin n → Nat) :
    xi_chain_interior_dirichlet_mobius_characteristic_closure_statement n q := by
  classical
  rcases paper_xi_chain_interior_godel_euler_mobius_factorization n q with
    ⟨_, _, hEuler, hMobius⟩
  refine ⟨hEuler, hMobius, ?_⟩
  intro x
  have hBoolean := paper_xi_chain_interior_boolean_flag_closed_form n
  rcases hBoolean with ⟨_, _, hsum, _, _⟩
  have hx :
      (∑ S : Finset (Fin (n - 1)), (-x) ^ S.card) = ((-x) + 1) ^ (n - 1) := by
    simpa using hsum (-x)
  calc
    (∑ S : Finset (Fin (n - 1)), (-1 : Int) ^ S.card * x ^ S.card)
        = ∑ S : Finset (Fin (n - 1)), (-x) ^ S.card := by
          refine Finset.sum_congr rfl ?_
          intro S _
          rw [← mul_pow]
          ring_nf
    _ = ((-x) + 1) ^ (n - 1) := hx
    _ = (1 - x) ^ (n - 1) := by ring_nf

end Omega.Zeta
