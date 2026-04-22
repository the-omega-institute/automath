import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Concrete data for the square-substitution discriminant split: `a` is the leading coefficient,
`rootProduct` packages the product of the original roots, and `pairProduct` packages the product
of the cross-pair root gaps in the original polynomial. -/
structure disc_square_substitution_split_data where
  d : ℕ
  a : ℂ
  rootProduct : ℂ
  pairProduct : ℂ
  hd : 1 ≤ d

/-- The same-pair contribution coming from the root pairs `±√α_j`. -/
def disc_square_substitution_split_same_pair_contribution
    (D : disc_square_substitution_split_data) : ℂ :=
  (4 : ℂ) ^ D.d * D.rootProduct

/-- The cross-pair contribution coming from distinct root pairs. -/
def disc_square_substitution_split_cross_pair_contribution
    (D : disc_square_substitution_split_data) : ℂ :=
  D.pairProduct ^ 2

/-- The constant term of the original polynomial. -/
def disc_square_substitution_split_constant_term
    (D : disc_square_substitution_split_data) : ℂ :=
  D.a * (-1 : ℂ) ^ D.d * D.rootProduct

/-- The original discriminant factor written through the leading coefficient and the cross-pair
product. -/
def disc_square_substitution_split_f_discriminant
    (D : disc_square_substitution_split_data) : ℂ :=
  D.a ^ (D.d - 1) * D.pairProduct

/-- The discriminant of the square-substituted polynomial after splitting same-pair and cross-pair
factors. -/
def disc_square_substitution_split_g_discriminant
    (D : disc_square_substitution_split_data) : ℂ :=
  D.a ^ (2 * D.d) * disc_square_substitution_split_same_pair_contribution D *
    disc_square_substitution_split_cross_pair_contribution D

/-- Paper-facing discriminant factorization for the square substitution. -/
def disc_square_substitution_split_data.discriminant_square_substitution_split
    (D : disc_square_substitution_split_data) : Prop :=
  disc_square_substitution_split_g_discriminant D =
    (-1 : ℂ) ^ D.d * (4 : ℂ) ^ D.d * D.a *
      disc_square_substitution_split_constant_term D *
      disc_square_substitution_split_f_discriminant D ^ 2

/-- Paper label: `lem:disc-square-substitution-split`. -/
theorem paper_disc_square_substitution_split (D : disc_square_substitution_split_data) :
    D.discriminant_square_substitution_split := by
  rcases D with ⟨d, a, rootProduct, pairProduct, hd⟩
  have hsign : ((-1 : ℂ) ^ d) * ((-1 : ℂ) ^ d) = 1 := by
    calc
      ((-1 : ℂ) ^ d) * ((-1 : ℂ) ^ d) = (((-1 : ℂ) ^ d) ^ 2) := by ring
      _ = (-1 : ℂ) ^ (d * 2) := by rw [← pow_mul]
      _ = 1 := by norm_num
  have hpow : a ^ (2 * d) = a ^ 2 * (a ^ (d - 1)) ^ 2 := by
    calc
      a ^ (2 * d) = a ^ (2 + 2 * (d - 1)) := by congr; omega
      _ = a ^ 2 * a ^ (2 * (d - 1)) := by rw [pow_add]
      _ = a ^ 2 * a ^ ((d - 1) * 2) := by simp [Nat.mul_comm]
      _ = a ^ 2 * (a ^ (d - 1)) ^ 2 := by rw [← pow_mul]
  unfold disc_square_substitution_split_data.discriminant_square_substitution_split
    disc_square_substitution_split_g_discriminant
    disc_square_substitution_split_same_pair_contribution
    disc_square_substitution_split_cross_pair_contribution
    disc_square_substitution_split_constant_term
    disc_square_substitution_split_f_discriminant
  rw [hpow]
  rw [mul_pow]
  symm
  calc
    (-1 : ℂ) ^ d * (4 : ℂ) ^ d * a * (a * (-1 : ℂ) ^ d * rootProduct) *
          ((a ^ (d - 1)) ^ 2 * pairProduct ^ 2)
        = (((-1 : ℂ) ^ d) * ((-1 : ℂ) ^ d)) * (4 : ℂ) ^ d * a * a * rootProduct *
            ((a ^ (d - 1)) ^ 2 * pairProduct ^ 2) := by
            ring
    _ = (4 : ℂ) ^ d * a * a * rootProduct * ((a ^ (d - 1)) ^ 2 * pairProduct ^ 2) := by
          rw [hsign]
          ring
    _ = a ^ 2 * (a ^ (d - 1)) ^ 2 * ((4 : ℂ) ^ d * rootProduct) * pairProduct ^ 2 := by
          ring
