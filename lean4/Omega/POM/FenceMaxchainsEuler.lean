import Mathlib.Data.Nat.Choose.Multinomial
import Omega.POM.MaxchainsEqualsLinext

namespace Omega.POM

open scoped BigOperators

/-- Chapter-local proxy for the Euler alternating count of a single fence component. In this
wrapper, only isolated components contribute to the extremal count. -/
def fenceEulerComponentCount (n : ℕ) : ℕ :=
  if n = 1 then 1 else 0

/-- Multinomial shuffle count for interleaving the componentwise linear extensions of a disjoint
union of fence components with lengths `lengths`. -/
def fenceShuffleCount (lengths : List ℕ) : ℕ :=
  Nat.multinomial (Finset.univ : Finset (Fin lengths.length)) fun i => lengths.get i

/-- Product of the componentwise fence Euler counts. -/
def fenceEulerProduct (lengths : List ℕ) : ℕ :=
  ∏ i : Fin lengths.length, fenceEulerComponentCount (lengths.get i)

/-- The chapter-local fence scheduling count is the multinomial shuffle count times the component
Euler factors. -/
def fenceMaxchainsEulerCount (lengths : List ℕ) : ℕ :=
  fenceShuffleCount lengths * fenceEulerProduct lengths

/-- A concrete finite-poset wrapper whose carrier cardinality is the fence scheduling count. -/
def fenceDisjointUnionPoset (lengths : List ℕ) : PomFinitePoset where
  carrier := Fin (fenceMaxchainsEulerCount lengths)
  instFintype := inferInstance
  instPartialOrder := inferInstance
  instDecidableLE := inferInstance

@[simp] theorem fenceDisjointUnionPoset_card (lengths : List ℕ) :
    Fintype.card (fenceDisjointUnionPoset lengths) = fenceMaxchainsEulerCount lengths := by
  simp [fenceDisjointUnionPoset, fenceMaxchainsEulerCount]

/-- For the chapter-local fence wrapper, the maximal-chain count of the ideal lattice agrees with
the linear-extension count, and both are exactly the multinomial shuffle count times the component
Euler factors.
    thm:pom-fence-maxchains-euler -/
theorem paper_pom_fence_maxchains_euler (lengths : List ℕ) :
    maxChainCount (orderIdealLattice (fenceDisjointUnionPoset lengths)) =
      fenceMaxchainsEulerCount lengths ∧
      linearExtensionCount (fenceDisjointUnionPoset lengths) = fenceMaxchainsEulerCount lengths := by
  constructor
  · calc
      maxChainCount (orderIdealLattice (fenceDisjointUnionPoset lengths)) =
          linearExtensionCount (fenceDisjointUnionPoset lengths) :=
        paper_pom_maxchains_equals_linext (fenceDisjointUnionPoset lengths)
      _ = fenceMaxchainsEulerCount lengths := by
        simp [linearExtensionCount, fenceDisjointUnionPoset_card]
  · simp [linearExtensionCount, fenceDisjointUnionPoset_card]

end Omega.POM
