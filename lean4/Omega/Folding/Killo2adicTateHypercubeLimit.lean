import Mathlib.Tactic
import Omega.Folding.KilloLeyang2powerTorsionCayleyHypercube

namespace Omega.Folding

/-- Restrict an `(n+1)`-bit block to its first `n` bits. -/
def killo_2adic_tate_hypercube_limit_truncate_bits (n : ℕ) (b : Fin (n + 1) → Bool) :
    Fin n → Bool :=
  fun i => b ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩

/-- Truncate the first address block by dropping its highest bit. -/
def killo_2adic_tate_hypercube_limit_truncate_firstBlock (n : ℕ)
    (ω : Omega.Word (2 * (n + 1))) : Fin n → Bool :=
  killo_2adic_tate_hypercube_limit_truncate_bits n
    (killo_leyang_2power_torsion_cayley_hypercube_firstBlock (n + 1) ω)

/-- Truncate the second address block by dropping its highest bit. -/
def killo_2adic_tate_hypercube_limit_truncate_secondBlock (n : ℕ)
    (ω : Omega.Word (2 * (n + 1))) : Fin n → Bool :=
  killo_2adic_tate_hypercube_limit_truncate_bits n
    (killo_leyang_2power_torsion_cayley_hypercube_secondBlock (n + 1) ω)

/-- Word-level truncation obtained by deleting the highest bit in each of the two blocks. -/
def killo_2adic_tate_hypercube_limit_truncate_word (n : ℕ) (ω : Omega.Word (2 * (n + 1))) :
    Omega.Word (2 * n) :=
  killo_leyang_2power_torsion_cayley_hypercube_joinBlocks n
    (killo_2adic_tate_hypercube_limit_truncate_firstBlock n ω)
    (killo_2adic_tate_hypercube_limit_truncate_secondBlock n ω)

/-- Coordinate truncation induced by keeping the lowest `n` binary digits. -/
def killo_2adic_tate_hypercube_limit_truncate_coordinate (n : ℕ) (a : ZMod (2 ^ (n + 1))) :
    ZMod (2 ^ n) :=
  Omega.CircleDimension.boolToZmodTwoPow n
    (killo_2adic_tate_hypercube_limit_truncate_bits n
      (Omega.CircleDimension.zmodTwoPowToBool (n + 1) a))

/-- Coordinatewise truncation on the pair model `(ZMod (2^(n+1)))^2`. -/
def killo_2adic_tate_hypercube_limit_truncate_pair (n : ℕ) :
    ZMod (2 ^ (n + 1)) × ZMod (2 ^ (n + 1)) → ZMod (2 ^ n) × ZMod (2 ^ n) :=
  fun p =>
    ( killo_2adic_tate_hypercube_limit_truncate_coordinate n p.1
    , killo_2adic_tate_hypercube_limit_truncate_coordinate n p.2 )

lemma killo_2adic_tate_hypercube_limit_firstBlock_truncate_word (n : ℕ)
    (ω : Omega.Word (2 * (n + 1))) :
    killo_leyang_2power_torsion_cayley_hypercube_firstBlock n
        (killo_2adic_tate_hypercube_limit_truncate_word n ω) =
      killo_2adic_tate_hypercube_limit_truncate_firstBlock n ω := by
  funext i
  simp [killo_2adic_tate_hypercube_limit_truncate_word,
    killo_leyang_2power_torsion_cayley_hypercube_firstBlock,
    killo_leyang_2power_torsion_cayley_hypercube_joinBlocks,
    killo_2adic_tate_hypercube_limit_truncate_firstBlock]

lemma killo_2adic_tate_hypercube_limit_secondBlock_truncate_word (n : ℕ)
    (ω : Omega.Word (2 * (n + 1))) :
    killo_leyang_2power_torsion_cayley_hypercube_secondBlock n
        (killo_2adic_tate_hypercube_limit_truncate_word n ω) =
      killo_2adic_tate_hypercube_limit_truncate_secondBlock n ω := by
  funext i
  have hi : ¬ n + i.1 < n := by omega
  have hidx : (n + i.1) - n = i.1 := by omega
  simp [killo_2adic_tate_hypercube_limit_truncate_word,
    killo_leyang_2power_torsion_cayley_hypercube_secondBlock,
    killo_leyang_2power_torsion_cayley_hypercube_joinBlocks,
    killo_2adic_tate_hypercube_limit_truncate_secondBlock, hi, hidx]

lemma killo_2adic_tate_hypercube_limit_truncate_coordinate_boolToZmodTwoPow
    (n : ℕ) (b : Fin (n + 1) → Bool) :
    killo_2adic_tate_hypercube_limit_truncate_coordinate n
        (Omega.CircleDimension.boolToZmodTwoPow (n + 1) b) =
      Omega.CircleDimension.boolToZmodTwoPow n
        (killo_2adic_tate_hypercube_limit_truncate_bits n b) := by
  unfold killo_2adic_tate_hypercube_limit_truncate_coordinate
  rw [Omega.CircleDimension.zmodTwoPowToBool_boolToZmodTwoPow]

/-- Paper label: `cor:killo-2adic-tate-hypercube-limit`. The finite-level hypercube address map
is bijective, and the truncation square commutes with the coordinate description obtained by
dropping the highest bit in each block. -/
theorem paper_killo_2adic_tate_hypercube_limit (n : Nat) :
    Function.Bijective (killo_leyang_2power_torsion_cayley_hypercube_address n) ∧
      ∀ ω : Omega.Word (2 * (n + 1)),
        killo_leyang_2power_torsion_cayley_hypercube_address n
            (killo_2adic_tate_hypercube_limit_truncate_word n ω) =
          killo_2adic_tate_hypercube_limit_truncate_pair n
            (killo_leyang_2power_torsion_cayley_hypercube_address (n + 1) ω) := by
  refine ⟨paper_killo_leyang_2power_torsion_cayley_hypercube n, ?_⟩
  intro ω
  ext <;>
    simp [killo_leyang_2power_torsion_cayley_hypercube_address,
      killo_2adic_tate_hypercube_limit_truncate_pair,
      killo_2adic_tate_hypercube_limit_firstBlock_truncate_word,
      killo_2adic_tate_hypercube_limit_secondBlock_truncate_word,
      killo_2adic_tate_hypercube_limit_truncate_coordinate_boolToZmodTwoPow,
      killo_2adic_tate_hypercube_limit_truncate_firstBlock,
      killo_2adic_tate_hypercube_limit_truncate_secondBlock]

end Omega.Folding
