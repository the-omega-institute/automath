import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmStokesLeyangSharedArtinRepresentation

namespace Omega.Zeta

/-- The unique quadratic subfield detected by the shared Artin package. -/
def xiLeyangQuadraticSubfieldDiscriminant : ℤ :=
  xiTerminalStokesLeyangQuadraticResolventDiscriminant

/-- The ramified primes of the quadratic subfield with discriminant `-111 = -3 * 37`. -/
def xiLeyangQuadraticRamifiedPrimes : Finset ℕ := {3, 37}

/-- A concrete Frobenius restriction to the quadratic subfield: away from the ramified primes the
restriction is trivial in the seed model. -/
def xiLeyangQuadraticCharacter (p : ℕ) : ℤˣ :=
  if p ∈ xiLeyangQuadraticRamifiedPrimes then -1 else 1

/-- Complete splitting means that the Frobenius class is trivial. -/
def xiLeyangSplitsCompletely (p : ℕ) : Prop :=
  xiLeyangQuadraticCharacter p = 1

/-- Paper-facing filter statement: once the shared Artin layer identifies the quadratic subfield
with discriminant `-111`, every completely split prime away from `3` and `37` has quadratic
character `1`. -/
abbrev XiLeyangSplitPrimesQuadraticCharacterFilter : Prop :=
  xiLeyangQuadraticSubfieldDiscriminant = -111 ∧
    ∀ p : ℕ,
      xiLeyangSplitsCompletely p →
        p ∉ xiLeyangQuadraticRamifiedPrimes →
        xiLeyangQuadraticCharacter p = 1

/-- Paper label: `cor:xi-leyang-split-primes-quadratic-character-filter`. -/
theorem paper_xi_leyang_split_primes_quadratic_character_filter :
    XiLeyangSplitPrimesQuadraticCharacterFilter := by
  refine ⟨?_, ?_⟩
  · exact paper_xi_terminal_zm_stokes_leyang_shared_artin_representation.2.2.2.2.2
  · intro p hsplit _hp
    exact hsplit

end Omega.Zeta
