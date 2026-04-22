import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.CircleDimension.DyadicKernelCube
import Omega.Core.WalshStokesSingleton

namespace Omega.Folding

open scoped BigOperators

/-- The first `n` bits of a `2n`-bit address. -/
def killo_leyang_2power_torsion_cayley_hypercube_firstBlock
    (n : ℕ) (ω : Omega.Word (2 * n)) : Fin n → Bool :=
  fun i => ω ⟨i.1, by omega⟩

/-- The second `n` bits of a `2n`-bit address. -/
def killo_leyang_2power_torsion_cayley_hypercube_secondBlock
    (n : ℕ) (ω : Omega.Word (2 * n)) : Fin n → Bool :=
  fun i => ω ⟨n + i.1, by omega⟩

/-- Reassemble a `2n`-bit word from two `n`-bit blocks. -/
def killo_leyang_2power_torsion_cayley_hypercube_joinBlocks
    (n : ℕ) (b c : Fin n → Bool) : Omega.Word (2 * n) :=
  fun i =>
    if h : i.1 < n then
      b ⟨i.1, h⟩
    else
      c ⟨i.1 - n, by omega⟩

/-- Binary address map into the coordinate model `(ZMod (2^n))^2`. -/
def killo_leyang_2power_torsion_cayley_hypercube_address
    (n : ℕ) (ω : Omega.Word (2 * n)) : ZMod (2 ^ n) × ZMod (2 ^ n) :=
  ( Omega.CircleDimension.boolToZmodTwoPow n
      (killo_leyang_2power_torsion_cayley_hypercube_firstBlock n ω)
  , Omega.CircleDimension.boolToZmodTwoPow n
      (killo_leyang_2power_torsion_cayley_hypercube_secondBlock n ω) )

/-- Decode a coordinate pair back to its two binary blocks. -/
def killo_leyang_2power_torsion_cayley_hypercube_decode
    (n : ℕ) (p : ZMod (2 ^ n) × ZMod (2 ^ n)) : Omega.Word (2 * n) :=
  killo_leyang_2power_torsion_cayley_hypercube_joinBlocks n
    (Omega.CircleDimension.zmodTwoPowToBool n p.1)
    (Omega.CircleDimension.zmodTwoPowToBool n p.2)

/-- The `j`-th basis bit in the first coordinate block. -/
def killo_leyang_2power_torsion_cayley_hypercube_firstIndex
    {n : ℕ} (j : Fin n) : Fin (2 * n) :=
  ⟨j.1, by omega⟩

/-- The `j`-th basis bit in the second coordinate block. -/
def killo_leyang_2power_torsion_cayley_hypercube_secondIndex
    {n : ℕ} (j : Fin n) : Fin (2 * n) :=
  ⟨n + j.1, by omega⟩

/-- Cayley generators coming from the first coordinate block. -/
def killo_leyang_2power_torsion_cayley_hypercube_firstGenerator
    (n : ℕ) (j : Fin n) : ZMod (2 ^ n) × ZMod (2 ^ n) :=
  ((2 ^ j.1 : ℕ), 0)

/-- Cayley generators coming from the second coordinate block. -/
def killo_leyang_2power_torsion_cayley_hypercube_secondGenerator
    (n : ℕ) (j : Fin n) : ZMod (2 ^ n) × ZMod (2 ^ n) :=
  (0, (2 ^ j.1 : ℕ))

/-- Symmetric generating set corresponding to one-bit flips in either block. -/
def killo_leyang_2power_torsion_cayley_hypercube_generatorSet (n : ℕ) :
    Set (ZMod (2 ^ n) × ZMod (2 ^ n)) :=
  {g | ∃ j : Fin n,
      g = killo_leyang_2power_torsion_cayley_hypercube_firstGenerator n j ∨
      g = -killo_leyang_2power_torsion_cayley_hypercube_firstGenerator n j ∨
      g = killo_leyang_2power_torsion_cayley_hypercube_secondGenerator n j ∨
      g = -killo_leyang_2power_torsion_cayley_hypercube_secondGenerator n j}

private lemma killo_leyang_2power_torsion_cayley_hypercube_joinBlocks_blocks
    (n : ℕ) (ω : Omega.Word (2 * n)) :
    killo_leyang_2power_torsion_cayley_hypercube_joinBlocks n
        (killo_leyang_2power_torsion_cayley_hypercube_firstBlock n ω)
        (killo_leyang_2power_torsion_cayley_hypercube_secondBlock n ω) = ω := by
  funext i
  by_cases h : i.1 < n
  · simp [killo_leyang_2power_torsion_cayley_hypercube_joinBlocks,
      killo_leyang_2power_torsion_cayley_hypercube_firstBlock, h]
  · have hi : n + (i.1 - n) = i.1 := by omega
    simp [killo_leyang_2power_torsion_cayley_hypercube_joinBlocks,
      killo_leyang_2power_torsion_cayley_hypercube_secondBlock, h, hi]

private lemma killo_leyang_2power_torsion_cayley_hypercube_decode_address
    (n : ℕ) (ω : Omega.Word (2 * n)) :
    killo_leyang_2power_torsion_cayley_hypercube_decode n
        (killo_leyang_2power_torsion_cayley_hypercube_address n ω) = ω := by
  unfold killo_leyang_2power_torsion_cayley_hypercube_decode
    killo_leyang_2power_torsion_cayley_hypercube_address
  rw [Omega.CircleDimension.zmodTwoPowToBool_boolToZmodTwoPow,
    Omega.CircleDimension.zmodTwoPowToBool_boolToZmodTwoPow]
  exact killo_leyang_2power_torsion_cayley_hypercube_joinBlocks_blocks n ω

private lemma killo_leyang_2power_torsion_cayley_hypercube_address_injective
    (n : ℕ) :
    Function.Injective (killo_leyang_2power_torsion_cayley_hypercube_address n) := by
  intro ω₁ ω₂ hω
  calc
    ω₁ = killo_leyang_2power_torsion_cayley_hypercube_decode n
        (killo_leyang_2power_torsion_cayley_hypercube_address n ω₁) := by
          symm
          exact killo_leyang_2power_torsion_cayley_hypercube_decode_address n ω₁
    _ = killo_leyang_2power_torsion_cayley_hypercube_decode n
        (killo_leyang_2power_torsion_cayley_hypercube_address n ω₂) := by
          simpa using congrArg (killo_leyang_2power_torsion_cayley_hypercube_decode n) hω
    _ = ω₂ := killo_leyang_2power_torsion_cayley_hypercube_decode_address n ω₂

private lemma killo_leyang_2power_torsion_cayley_hypercube_card_eq
    (n : ℕ) :
    Fintype.card (Omega.Word (2 * n)) = Fintype.card (ZMod (2 ^ n) × ZMod (2 ^ n)) := by
  change Fintype.card (Fin (2 * n) → Bool) = Fintype.card (ZMod (2 ^ n) × ZMod (2 ^ n))
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Fintype.card_prod, ZMod.card]
  simpa [two_mul] using (pow_add 2 n n)

/-- Paper label: `thm:killo-leyang-2power-torsion-cayley-hypercube`. The explicit binary address
map from two length-`n` bit blocks into `(ZMod (2^n))^2` is bijective. -/
theorem paper_killo_leyang_2power_torsion_cayley_hypercube (n : ℕ) :
    Function.Bijective (killo_leyang_2power_torsion_cayley_hypercube_address n) := by
  exact (Fintype.bijective_iff_injective_and_card
      (killo_leyang_2power_torsion_cayley_hypercube_address n)).2
    ⟨killo_leyang_2power_torsion_cayley_hypercube_address_injective n,
      killo_leyang_2power_torsion_cayley_hypercube_card_eq n⟩

end Omega.Folding
