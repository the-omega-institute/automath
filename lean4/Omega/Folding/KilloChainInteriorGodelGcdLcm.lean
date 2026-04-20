import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic
import Omega.Core.FiberLatticeSquarefree

namespace Omega.Folding

/-- The `i`-th prime used to squarefree-code the fixed-point set of a chain interior operator. -/
noncomputable def chainInteriorPrime {n : ℕ} (i : Fin n) : ℕ :=
  Nat.nth Nat.Prime i

theorem chainInteriorPrime_prime {n : ℕ} (i : Fin n) : Nat.Prime (chainInteriorPrime i) := by
  simp [chainInteriorPrime]

theorem chainInteriorPrime_injective {n : ℕ} : Function.Injective (@chainInteriorPrime n) := by
  intro i j hij
  apply Fin.ext
  exact (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hij

/-- Squarefree Gödel code of a fixed-point set on the `(n + 1)`-element chain. -/
noncomputable def chainInteriorGodelCode {n : ℕ} (F : Finset (Fin (n + 1))) : ℕ :=
  Omega.POM.fiberLatticePhi chainInteriorPrime F

/-- Concrete arithmetic seed for the chain-interior theorem: on fixed-point sets containing `0`,
the squarefree Gödel code transports intersection/union to `gcd`/`lcm`. -/
def ChainInteriorGodelGcdLcm (n : ℕ) : Prop :=
  ∀ F G : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∈ F → (0 : Fin (n + 1)) ∈ G →
    chainInteriorGodelCode (F ∩ G) = Nat.gcd (chainInteriorGodelCode F) (chainInteriorGodelCode G) ∧
      chainInteriorGodelCode (F ∪ G) =
        Nat.lcm (chainInteriorGodelCode F) (chainInteriorGodelCode G)

/-- The fixed-point sets of chain interior operators are the subsets containing `0`, and the
squarefree Gödel code turns their meet/join arithmetic into `gcd`/`lcm`. -/
theorem paper_killo_chain_interior_godel_gcd_lcm (n : ℕ) : ChainInteriorGodelGcdLcm n := by
  intro F G hF hG
  rcases Omega.POM.paper_fiber_lattice_squarefree_prime_register_gcd_lcm
      (q := @chainInteriorPrime (n + 1)) chainInteriorPrime_prime chainInteriorPrime_injective with
    ⟨_, _, hinter, hunion⟩
  exact ⟨hinter F G, hunion F G⟩

end Omega.Folding
