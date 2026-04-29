import Mathlib.Tactic
import Omega.EA.PrimeRegisterFibValuation

namespace Omega.POM.DoubleTransversalNormalForm

open Finsupp

/-- Configuration space: finitely supported functions `ℕ → ℕ`.
    thm:pom-double-transversal-normal-form -/
abbrev Config := ℕ →₀ ℕ

/-- Integer valuation of a configuration (lifted from `valPr`).
    thm:pom-double-transversal-normal-form -/
noncomputable def val (a : Config) : ℕ := Omega.EA.valPr a

/-- Symmetric remainder in roughly `(-⌊b/2⌋, ⌊b/2⌋]`.
    thm:pom-double-transversal-normal-form -/
noncomputable def symRem (n : ℤ) (b : ℕ) : ℤ :=
  if n % (b : ℤ) ≤ (b : ℤ) / 2 then n % (b : ℤ) else n % (b : ℤ) - b

/-- Symmetric quotient consistent with `symRem`.
    thm:pom-double-transversal-normal-form -/
noncomputable def symQuo (n : ℤ) (b : ℕ) : ℤ :=
  if n % (b : ℤ) ≤ (b : ℤ) / 2 then n / (b : ℤ) else n / (b : ℤ) + 1

/-- Decomposition: `n = symQuo · b + symRem`.
    thm:pom-double-transversal-normal-form -/
theorem symQuoRem_spec (n : ℤ) (b : ℕ) (hb : 0 < b) :
    n = symQuo n b * b + symRem n b := by
  unfold symQuo symRem
  have hbz : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  have hdiv0 : (b : ℤ) * (n / (b : ℤ)) + n % (b : ℤ) = n :=
    Int.mul_ediv_add_emod n (b : ℤ)
  have hdiv : n / (b : ℤ) * (b : ℤ) + n % (b : ℤ) = n := by
    rw [mul_comm]; exact hdiv0
  split_ifs with h
  · linarith
  · linarith

/-- Symmetric remainder is at most `⌊b/2⌋`.
    thm:pom-double-transversal-normal-form -/
theorem symRem_le (n : ℤ) (b : ℕ) (hb : 0 < b) :
    symRem n b ≤ (b : ℤ) / 2 := by
  unfold symRem
  have hbz : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  have hmod_lt : n % (b : ℤ) < (b : ℤ) := Int.emod_lt_of_pos n hbz
  have hmod_nn : 0 ≤ n % (b : ℤ) := Int.emod_nonneg n (ne_of_gt hbz)
  split_ifs with h
  · exact h
  · push_neg at h
    omega

/-- Symmetric remainder is strictly greater than `-⌊b/2⌋ - 1` (i.e., ≥ -⌊b/2⌋ for even b,
    ≥ -⌊(b-1)/2⌋ for odd b).
    thm:pom-double-transversal-normal-form -/
theorem symRem_ge (n : ℤ) (b : ℕ) (hb : 0 < b) :
    -((b : ℤ) / 2) ≤ symRem n b := by
  unfold symRem
  have hbz : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  have hmod_lt : n % (b : ℤ) < (b : ℤ) := Int.emod_lt_of_pos n hbz
  have hmod_nn : 0 ≤ n % (b : ℤ) := Int.emod_nonneg n (ne_of_gt hbz)
  split_ifs with h
  · -- n % b ≤ b/2; want -(b/2) ≤ n % b, which follows from 0 ≤ n % b
    linarith
  · -- n % b > b/2; want -(b/2) ≤ n % b - b
    push_neg at h
    omega

/-- Paper package: existence of the symmetric (q, r) decomposition.
    thm:pom-double-transversal-normal-form -/
theorem paper_pom_double_transversal_normal_form
    (a : Config) (b : ℕ) (hb : 0 < b) :
    ∃ (q r : ℤ),
      (val a : ℤ) = q * b + r ∧
      -((b : ℤ) / 2) ≤ r ∧ r ≤ (b : ℤ) / 2 := by
  refine ⟨symQuo (val a : ℤ) b, symRem (val a : ℤ) b, ?_, ?_, ?_⟩
  · exact symQuoRem_spec (val a : ℤ) b hb
  · exact symRem_ge (val a : ℤ) b hb
  · exact symRem_le (val a : ℤ) b hb

/-- Standard quotient-remainder normal form with a unique remainder in `[0,b)`.
    thm:pom-double-transversal-normal-form -/
theorem paper_pom_double_transversal_normal_form_unique_standard (a : Config) (b : ℕ)
    (hb : 0 < b) :
    ∃! qr : ℤ × ℤ, (val a : ℤ) = qr.1 * (b : ℤ) + qr.2 ∧
      0 ≤ qr.2 ∧ qr.2 < (b : ℤ) := by
  let n : ℤ := val a
  let bz : ℤ := b
  have hbz : 0 < bz := by
    dsimp [bz]
    exact_mod_cast hb
  have hbz_ne : bz ≠ 0 := ne_of_gt hbz
  let q0 : ℤ := n / bz
  let r0 : ℤ := n % bz
  have hdecomp0 : n = q0 * bz + r0 := by
    dsimp [q0, r0]
    rw [mul_comm]
    exact (Int.mul_ediv_add_emod n bz).symm
  refine ⟨(q0, r0), ?_, ?_⟩
  · constructor
    · simpa [n, bz, q0, r0] using hdecomp0
    · exact ⟨Int.emod_nonneg n hbz_ne, Int.emod_lt_of_pos n hbz⟩
  · rintro ⟨q, r⟩ ⟨hqr, hr_nonneg, hr_lt⟩
    have hqr' : n = q * bz + r := by
      simpa [n, bz] using hqr
    have hr_eq : r0 = r := by
      calc
        r0 = n % bz := rfl
        _ = (q * bz + r) % bz := by rw [hqr']
        _ = (r + bz * q) % bz := by ring_nf
        _ = r % bz := by rw [Int.add_mul_emod_self_left]
        _ = r := Int.emod_eq_of_lt hr_nonneg hr_lt
    have hq_mul : q * bz = q0 * bz := by
      linarith
    have hq_eq : q = q0 := mul_right_cancel₀ hbz_ne hq_mul
    ext <;> simp [hq_eq, hr_eq]

end Omega.POM.DoubleTransversalNormalForm
