import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open scoped goldenRatio

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9y-audited-even-minsector-golden-defect-law`. -/
theorem paper_xi_time_part9y_audited_even_minsector_golden_defect_law
    (m sectorCard complementCard ambientCard D : ℕ) (hm : m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12)
    (hsector : sectorCard = Nat.fib m) (hcomplement : complementCard = Nat.fib (m + 1))
    (hambient : ambientCard = Nat.fib (m + 2)) (hD : D = complementCard) :
    (sectorCard : ℝ) / ambientCard =
        (φ : ℝ)⁻¹ * φ⁻¹ - 1 / ((φ : ℝ) ^ (m + 2) * Nat.fib (m + 2)) ∧
      (complementCard : ℝ) / ambientCard =
        (φ : ℝ)⁻¹ + 1 / ((φ : ℝ) ^ (m + 2) * Nat.fib (m + 2)) ∧
        (D : ℝ) / ambientCard = (complementCard : ℝ) / ambientCard := by
  subst sectorCard
  subst complementCard
  subst ambientCard
  subst D
  let x : ℝ := (φ : ℝ)
  have hx : x ^ 2 = x + 1 := by simp [x]
  have hx0 : x ≠ 0 := by simpa [x] using Real.goldenRatio_ne_zero
  have h3 : x ^ 3 = 2 * x + 1 := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _ = 2 * x + 1 := by
        rw [hx]
        ring_nf
        nlinarith [hx]
  have h4 : x ^ 4 = 3 * x + 2 := by
    calc
      x ^ 4 = x * x ^ 3 := by ring
      _ = x * (2 * x + 1) := by rw [h3]
      _ = 3 * x + 2 := by
        ring_nf
        nlinarith [hx]
  have h5 : x ^ 5 = 5 * x + 3 := by
    calc
      x ^ 5 = x * x ^ 4 := by ring
      _ = x * (3 * x + 2) := by rw [h4]
      _ = 5 * x + 3 := by
        ring_nf
        nlinarith [hx]
  have h6 : x ^ 6 = 8 * x + 5 := by
    calc
      x ^ 6 = x * x ^ 5 := by ring
      _ = x * (5 * x + 3) := by rw [h5]
      _ = 8 * x + 5 := by
        ring_nf
        nlinarith [hx]
  have h7 : x ^ 7 = 13 * x + 8 := by
    calc
      x ^ 7 = x * x ^ 6 := by ring
      _ = x * (8 * x + 5) := by rw [h6]
      _ = 13 * x + 8 := by
        ring_nf
        nlinarith [hx]
  have h8 : x ^ 8 = 21 * x + 13 := by
    calc
      x ^ 8 = x * x ^ 7 := by ring
      _ = x * (13 * x + 8) := by rw [h7]
      _ = 21 * x + 13 := by
        ring_nf
        nlinarith [hx]
  have h9 : x ^ 9 = 34 * x + 21 := by
    calc
      x ^ 9 = x * x ^ 8 := by ring
      _ = x * (21 * x + 13) := by rw [h8]
      _ = 34 * x + 21 := by
        ring_nf
        nlinarith [hx]
  have h10 : x ^ 10 = 55 * x + 34 := by
    calc
      x ^ 10 = x * x ^ 9 := by ring
      _ = x * (34 * x + 21) := by rw [h9]
      _ = 55 * x + 34 := by
        ring_nf
        nlinarith [hx]
  have h11 : x ^ 11 = 89 * x + 55 := by
    calc
      x ^ 11 = x * x ^ 10 := by ring
      _ = x * (55 * x + 34) := by rw [h10]
      _ = 89 * x + 55 := by
        ring_nf
        nlinarith [hx]
  have h12 : x ^ 12 = 144 * x + 89 := by
    calc
      x ^ 12 = x * x ^ 11 := by ring
      _ = x * (89 * x + 55) := by rw [h11]
      _ = 144 * x + 89 := by
        ring_nf
        nlinarith [hx]
  have h13 : x ^ 13 = 233 * x + 144 := by
    calc
      x ^ 13 = x * x ^ 12 := by ring
      _ = x * (144 * x + 89) := by rw [h12]
      _ = 233 * x + 144 := by
        ring_nf
        nlinarith [hx]
  have h14 : x ^ 14 = 377 * x + 233 := by
    calc
      x ^ 14 = x * x ^ 13 := by ring
      _ = x * (233 * x + 144) := by rw [h13]
      _ = 377 * x + 233 := by
        ring_nf
        nlinarith [hx]
  rcases hm with rfl | rfl | rfl | rfl
  · constructor
    · change (8 : ℝ) / 21 = x⁻¹ * x⁻¹ - 1 / (x ^ (6 + 2) * Nat.fib (6 + 2))
      norm_num [Nat.fib_add_two]
      field_simp [hx0]
      rw [h8]
      ring_nf
      nlinarith [hx]
    · constructor
      · change (13 : ℝ) / 21 = x⁻¹ + 1 / (x ^ (6 + 2) * Nat.fib (6 + 2))
        norm_num [Nat.fib_add_two]
        field_simp [hx0]
        rw [h8]
        ring_nf
        nlinarith [hx]
      · rfl
  · constructor
    · change (21 : ℝ) / 55 = x⁻¹ * x⁻¹ - 1 / (x ^ (8 + 2) * Nat.fib (8 + 2))
      norm_num [Nat.fib_add_two]
      field_simp [hx0]
      rw [h10]
      ring_nf
      nlinarith [hx]
    · constructor
      · change (34 : ℝ) / 55 = x⁻¹ + 1 / (x ^ (8 + 2) * Nat.fib (8 + 2))
        norm_num [Nat.fib_add_two]
        field_simp [hx0]
        rw [h10]
        ring_nf
        nlinarith [hx]
      · rfl
  · constructor
    · change (55 : ℝ) / 144 = x⁻¹ * x⁻¹ - 1 / (x ^ (10 + 2) * Nat.fib (10 + 2))
      norm_num [Nat.fib_add_two]
      field_simp [hx0]
      rw [h12]
      ring_nf
      nlinarith [hx]
    · constructor
      · change (89 : ℝ) / 144 = x⁻¹ + 1 / (x ^ (10 + 2) * Nat.fib (10 + 2))
        norm_num [Nat.fib_add_two]
        field_simp [hx0]
        rw [h12]
        ring_nf
        nlinarith [hx]
      · rfl
  · constructor
    · change (144 : ℝ) / 377 = x⁻¹ * x⁻¹ - 1 / (x ^ (12 + 2) * Nat.fib (12 + 2))
      norm_num [Nat.fib_add_two]
      field_simp [hx0]
      rw [h14]
      ring_nf
      nlinarith [hx]
    · constructor
      · change (233 : ℝ) / 377 = x⁻¹ + 1 / (x ^ (12 + 2) * Nat.fib (12 + 2))
        norm_num [Nat.fib_add_two]
        field_simp [hx0]
        rw [h14]
        ring_nf
        nlinarith [hx]
      · rfl

end Omega.Zeta
