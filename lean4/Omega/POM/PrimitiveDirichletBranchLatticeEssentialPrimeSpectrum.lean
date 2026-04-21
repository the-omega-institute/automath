import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete branch-lattice package for the primitive Dirichlet series: `branchOccurs p m`
registers the branch-point family attached to the `p`-th Möbius term. -/
structure PrimitiveDirichletBranchLatticeData where
  branchOccurs : ℕ → ℤ → Prop
  oddPrimeBranch : ∀ ⦃p : ℕ⦄, Nat.Prime p → p ≠ 2 → ∀ m : ℤ, branchOccurs p m
  noEvenPrimeBranch : ∀ m : ℤ, ¬ branchOccurs 2 m
  nonprimeNoBranch : ∀ ⦃p : ℕ⦄, ¬ Nat.Prime p → ∀ m : ℤ, ¬ branchOccurs p m

namespace PrimitiveDirichletBranchLatticeData

/-- The analytic essential prime spectrum extracted from the branch-point lattice. -/
def analyticEssentialPrimeSpectrum (D : PrimitiveDirichletBranchLatticeData) : Set ℕ :=
  {p | ∃ m : ℤ, D.branchOccurs p m}

end PrimitiveDirichletBranchLatticeData

open PrimitiveDirichletBranchLatticeData

/-- Paper-facing characterization of the analytic essential prime spectrum by the odd primes.
    thm:pom-primitive-dirichlet-branch-lattice-an-essential-prime-spectrum -/
theorem paper_pom_primitive_dirichlet_branch_lattice_essential_prime_spectrum
    (D : PrimitiveDirichletBranchLatticeData) :
    D.analyticEssentialPrimeSpectrum = {p | Nat.Prime p ∧ p ≠ 2} := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨m, hm⟩
    by_cases hprime : Nat.Prime p
    · refine ⟨hprime, ?_⟩
      intro hp2
      subst hp2
      exact D.noEvenPrimeBranch m hm
    · exact False.elim <| D.nonprimeNoBranch hprime m hm
  · intro hp
    rcases hp with ⟨hprime, hne2⟩
    exact ⟨0, D.oddPrimeBranch hprime hne2 0⟩

end Omega.POM
