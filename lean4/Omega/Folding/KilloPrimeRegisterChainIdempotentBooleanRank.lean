import Mathlib

namespace Omega.Folding

open Finset

/-- Intersections of a finite family of subsets of `Fin m`, indexed by a finite set of
coordinates. -/
def booleanMeetOfFamily {m r : ℕ} (A : Finset (Fin r)) (G : Fin r → Finset (Fin m)) :
    Finset (Fin m) :=
  Finset.univ.filter fun x => ∀ i ∈ A, x ∈ G i

/-- The `j`-th Boolean generator is the complement of the singleton `{j}`. -/
def chainBooleanGenerator (m : ℕ) (j : Fin m) : Finset (Fin m) :=
  Finset.univ.erase j

/-- Concrete Boolean-rank statement for the chain-idempotent meet semilattice model. -/
def PrimeRegisterChainIdempotentBooleanRank (n : ℕ) : Prop :=
  let m := n - 1
  (∀ F : Finset (Fin m),
      booleanMeetOfFamily
          (Finset.univ.filter fun j : Fin m => j ∉ F)
          (chainBooleanGenerator m) = F) ∧
    ∀ r : ℕ, ∀ G : Fin r → Finset (Fin m),
      (∀ F : Finset (Fin m), ∃ A : Finset (Fin r), booleanMeetOfFamily A G = F) →
        m ≤ r

theorem booleanMeetOfFamily_missing_coordinates (m : ℕ) (F : Finset (Fin m)) :
    booleanMeetOfFamily
        (Finset.univ.filter fun j : Fin m => j ∉ F)
        (chainBooleanGenerator m) = F := by
  classical
  ext x
  by_cases hx : x ∈ F
  · simp [booleanMeetOfFamily, chainBooleanGenerator, hx]
    intro i hi hxi
    subst hxi
    exact hi hx
  · simp [booleanMeetOfFamily, chainBooleanGenerator, hx]

theorem boolean_generator_family_minimal (m r : ℕ) (G : Fin r → Finset (Fin m))
    (hG : ∀ F : Finset (Fin m), ∃ A : Finset (Fin r), booleanMeetOfFamily A G = F) :
    m ≤ r := by
  classical
  let encode : Finset (Fin r) → Finset (Fin m) := fun A => booleanMeetOfFamily A G
  have hsurj : Function.Surjective encode := by
    intro F
    simpa [encode] using hG F
  have hcard : Fintype.card (Finset (Fin m)) ≤ Fintype.card (Finset (Fin r)) :=
    Fintype.card_le_of_surjective encode hsurj
  have hpow : 2 ^ m ≤ 2 ^ r := by
    simpa [Fintype.card_finset, Fintype.card_fin] using hcard
  exact (Nat.pow_le_pow_iff_right (by decide : 2 ≤ 2)).mp hpow

/-- The Boolean meet-semilattice on the missing coordinates of the chain has rank `n - 1`:
the singleton complements generate all subsets, and any generating family needs at least
`n - 1` generators. -/
theorem paper_killo_prime_register_chain_idempotent_boolean_rank (n : ℕ) :
    PrimeRegisterChainIdempotentBooleanRank n := by
  classical
  refine ⟨?_, ?_⟩
  · intro F
    simpa [PrimeRegisterChainIdempotentBooleanRank] using
      booleanMeetOfFamily_missing_coordinates (n - 1) F
  · intro r G hG
    simpa [PrimeRegisterChainIdempotentBooleanRank] using
      boolean_generator_family_minimal (n - 1) r G hG

end Omega.Folding
