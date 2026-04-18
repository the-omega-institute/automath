import Mathlib.Tactic
import Omega.CircleDimension.PhaseSeparationPrecisionExponent

namespace Omega.CircleDimension.CoprimeFractionLowerBound

open Finset
open Omega.CircleDimension.PhaseSeparationPrecisionExponent

/-- Coprime pairs `(a, b)` with `1 ≤ a, b ≤ B` and `gcd(a, b) = 1`.
    prop:cdim-bounded-height-rationals-separation -/
def coprimePairs (B : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B)).filter (fun p => Nat.gcd p.1 p.2 = 1)

/-- The first column `{(a, 1) : 1 ≤ a ≤ B}`.
    prop:cdim-bounded-height-rationals-separation -/
def firstColumn (B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 B).image (fun a => (a, 1))

/-- The first column is contained in the coprime pairs (since `gcd(a, 1) = 1`).
    prop:cdim-bounded-height-rationals-separation -/
theorem firstColumn_subset_coprimePairs (B : ℕ) :
    firstColumn B ⊆ coprimePairs B := by
  intro p hp
  unfold firstColumn at hp
  unfold coprimePairs
  rw [Finset.mem_image] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_product]
    refine ⟨ha, ?_⟩
    rw [Finset.mem_Icc]
    rw [Finset.mem_Icc] at ha
    refine ⟨le_refl 1, ?_⟩
    show 1 ≤ B
    omega
  · exact Nat.gcd_one_right a

/-- The first column has cardinality `B` (B = 0 gives 0).
    prop:cdim-bounded-height-rationals-separation -/
theorem firstColumn_card (B : ℕ) : (firstColumn B).card = B := by
  unfold firstColumn
  rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
  rw [Nat.card_Icc]
  omega

/-- Lower bound: `B ≤ |coprimePairs B|`.
    prop:cdim-bounded-height-rationals-separation -/
theorem coprimePairs_card_ge_B (B : ℕ) : B ≤ (coprimePairs B).card := by
  have h1 : (firstColumn B).card ≤ (coprimePairs B).card :=
    Finset.card_le_card (firstColumn_subset_coprimePairs B)
  rw [firstColumn_card] at h1
  exact h1

/-- Paper package: bounded-height rationals separation (lower B form).
    prop:cdim-bounded-height-rationals-separation -/
theorem paper_cdim_bounded_height_rationals_separation_lower_B (B : ℕ) :
    B ≤ (coprimePairs B).card :=
  coprimePairs_card_ge_B B

/-- Concrete finite witness package for the bounded-height rationals counting and finite-grid
packing comparison. -/
structure BoundedHeightRationalsSeparationData where
  B : ℕ
  k : ℕ
  L : ℕ
  lowerEmbedding : Fin (B ^ 2 / 4) → coprimePairs B
  lowerEmbedding_injective : Function.Injective lowerEmbedding
  upperEmbedding : coprimePairs B → Fin (gridBinCount k L)
  upperEmbedding_injective : Function.Injective upperEmbedding

/-- Concrete lower cardinality bound attached to a finite witness package. -/
def BoundedHeightRationalsSeparationData.cardLowerBound
    (D : BoundedHeightRationalsSeparationData) : Prop :=
  D.B ^ 2 / 4 ≤ (coprimePairs D.B).card

/-- Concrete torus-packing upper bound attached to a finite witness package. -/
def BoundedHeightRationalsSeparationData.separationUpperBound
    (D : BoundedHeightRationalsSeparationData) : Prop :=
  (coprimePairs D.B).card ≤ gridBinCount D.k D.L

/-- Paper package: bounded-height rationals separation.
    prop:cdim-bounded-height-rationals-separation -/
theorem paper_cdim_bounded_height_rationals_separation (D : BoundedHeightRationalsSeparationData) :
    D.cardLowerBound ∧ D.separationUpperBound := by
  constructor
  · simpa [BoundedHeightRationalsSeparationData.cardLowerBound] using
      (Fintype.card_le_of_injective D.lowerEmbedding D.lowerEmbedding_injective)
  · have hpack :=
      paper_cdim_torus_packing_bound (E := coprimePairs D.B) D.k D.L
        ⟨D.upperEmbedding, D.upperEmbedding_injective⟩
    simpa [BoundedHeightRationalsSeparationData.separationUpperBound] using hpack.1

end Omega.CircleDimension.CoprimeFractionLowerBound
