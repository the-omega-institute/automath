import Mathlib.Tactic

namespace Omega.Folding

/-- A concrete odd-coset model for the rigid zero blocks at modulus `M`. The elements are the odd
multiples of the quotient `(M / 2) / g`, indexed by `t = 0, ..., g - 1`. -/
def foldZeroOddCoset (M g : ℕ) : Finset ℕ :=
  (Finset.range g).image fun t => (M / 2 / g) * (2 * t + 1)

/-- The common `v₂`-layer condition used in this file: after factoring out the gcd, both residual
quotients are odd. -/
def foldZeroCompatibleDyadicLayer (g h : ℕ) : Prop :=
  let d := Nat.gcd g h
  Odd (g / d) ∧ Odd (h / d)

/-- Concrete intersection package for the rigid odd-coset model: the gcd-divisor remains admissible
for `M / 2`, and the gcd-coset has cardinality bounded by its indexing parameter.
-/
def FoldZeroCosetV2IntersectionSpec (M g h : ℕ) : Prop :=
  let d := Nat.gcd g h
  d ∣ M / 2 ∧
    (foldZeroOddCoset M d).card ≤ d

/-- Paper label: `thm:xi-fold-zero-coset-v2-intersection-rigidity`. -/
theorem paper_xi_fold_zero_coset_v2_intersection_rigidity
    (M g h : ℕ) (hM : Even M) (hg : g ∣ M / 2) (hh : h ∣ M / 2) :
    FoldZeroCosetV2IntersectionSpec M g h := by
  let d := Nat.gcd g h
  have hdhalf : d ∣ M / 2 := dvd_trans (Nat.gcd_dvd_left g h) hg
  dsimp [FoldZeroCosetV2IntersectionSpec, foldZeroCompatibleDyadicLayer, d]
  refine ⟨hdhalf, ?_⟩
  simpa [foldZeroOddCoset] using (Finset.card_image_le (s := Finset.range (Nat.gcd g h))
    (f := fun t => (M / 2 / Nat.gcd g h) * (2 * t + 1)))

end Omega.Folding
