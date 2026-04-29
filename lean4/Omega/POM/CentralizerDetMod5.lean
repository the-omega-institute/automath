import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Omega.Graph.TransferMatrix

namespace Omega.POM.CentralizerDetMod5

open Matrix
open Polynomial
open scoped Polynomial

/-- Centralizer determinant formula: det(aI + bA) = a² + ab - b².
    prop:pom-centralizer-det-norm-mod5 -/
theorem centralizer_det_formula (a b : ℤ) :
    (a • (1 : Matrix (Fin 2) (Fin 2) ℤ) + b • Graph.goldenMeanAdjacency).det =
      a ^ 2 + a * b - b ^ 2 := by
  simp only [det_fin_two]
  simp only [Graph.goldenMeanAdjacency, smul_apply, one_apply, add_apply,
    Fin.isValue]
  norm_num
  ring

/-- The centralizer determinant mod 5 is a perfect square mod 5.
    prop:pom-centralizer-det-norm-mod5 -/
theorem det_mod5_is_square (a b : ℤ) :
    (a ^ 2 + a * b - b ^ 2) % 5 = ((a + 3 * b) ^ 2) % 5 := by
  have : (a + 3 * b) ^ 2 - (a ^ 2 + a * b - b ^ 2) = 5 * (a * b + 2 * b ^ 2) := by ring
  omega

/-- The golden-ratio minimal polynomial has discriminant 5.
    prop:pom-centralizer-det-norm-mod5 -/
theorem golden_ratio_discriminant : 1 ^ 2 + 4 * 1 = 5 := by norm_num

/-- The golden-ratio polynomial x² - x - 1 factors as (x - 3)² over Z/5.
    prop:pom-centralizer-det-norm-mod5 -/
theorem golden_poly_mod5_double_root :
    ∀ τ : ZMod 5, τ ^ 2 - τ - 1 = (τ - 3) ^ 2 := by decide

/-- The integral centralizer of the golden mean adjacency matrix consists exactly of
`a • 1 + b • M`.  Paper label: `prop:pom-centralizer-det-norm-mod5`. -/
theorem pom_centralizer_det_norm_mod5_centralizer_unique :
    ∀ A : Matrix (Fin 2) (Fin 2) ℤ,
      A * Graph.goldenMeanAdjacency = Graph.goldenMeanAdjacency * A →
        ∃! ab : ℤ × ℤ,
          A = ab.1 • (1 : Matrix (Fin 2) (Fin 2) ℤ) + ab.2 • Graph.goldenMeanAdjacency := by
  intro A hcomm
  refine ⟨(A 1 1, A 0 1), ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j
    · have h01 := congr_fun (congr_fun hcomm 0) 1
      simp [Graph.goldenMeanAdjacency, Matrix.mul_apply, Fin.sum_univ_two] at h01
      simpa [Graph.goldenMeanAdjacency, Matrix.intCast_apply, add_comm] using h01
    · simp [Graph.goldenMeanAdjacency, Matrix.intCast_apply]
    · have h00 := congr_fun (congr_fun hcomm 0) 0
      simp [Graph.goldenMeanAdjacency, Matrix.mul_apply, Fin.sum_univ_two] at h00
      simpa [Graph.goldenMeanAdjacency, Matrix.intCast_apply] using h00.symm
    · simp [Graph.goldenMeanAdjacency, Matrix.intCast_apply]
  · intro ab hab
    ext
    · have h11 := congr_fun (congr_fun hab 1) 1
      simpa [Graph.goldenMeanAdjacency, Matrix.intCast_apply] using h11.symm
    · have h01 := congr_fun (congr_fun hab 0) 1
      simpa [Graph.goldenMeanAdjacency, Matrix.intCast_apply] using h01.symm

/-- Paper seeds: centralizer determinant at small values.
    prop:pom-centralizer-det-norm-mod5 -/
theorem paper_pom_centralizer_det_mod5 :
    (1 ^ 2 + 1 * 0 - 0 ^ 2 = (1 : ℤ)) ∧
    (0 ^ 2 + 0 * 1 - 1 ^ 2 = (-1 : ℤ)) ∧
    (1 ^ 2 + 1 * 1 - 1 ^ 2 = (1 : ℤ)) ∧
    (2 ^ 2 + 2 * 1 - 1 ^ 2 = (5 : ℤ)) ∧
    (1 ^ 2 + 4 * 1 = 5) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The mod-`5` reduction is the unique prime where the golden-ratio polynomial acquires a
double root.  Paper label: `cor:pom-centralizer-unique-bad-prime-5`. -/
theorem paper_pom_centralizer_unique_bad_prime_5 :
    (∀ τ : ZMod 5, τ ^ 2 - τ - 1 = (τ - 3) ^ 2) ∧
      ¬∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ ∀ τ : ZMod p, τ ^ 2 - τ - 1 = (τ - 3) ^ 2 := by
  refine ⟨golden_poly_mod5_double_root, ?_⟩
  rintro ⟨p, hp, hp_ne, hsquare⟩
  have hfive_zmod : (5 : ZMod p) = 0 := by
    have h1 := hsquare (1 : ZMod p)
    norm_num at h1
    have h2 := congrArg (fun z : ZMod p => z + 1) h1
    norm_num at h2
    simpa using h2.symm
  have hpdvd : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp hfive_zmod
  have hp_eq : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp hpdvd
  exact hp_ne hp_eq

/-- Paper label: `prop:pom-centralizer-det-norm-mod5`. -/
theorem paper_pom_centralizer_det_norm_mod5 :
    (∀ A : Matrix (Fin 2) (Fin 2) ℤ,
      A * Graph.goldenMeanAdjacency = Graph.goldenMeanAdjacency * A →
        ∃! ab : ℤ × ℤ,
          A = ab.1 • (1 : Matrix (Fin 2) (Fin 2) ℤ) + ab.2 • Graph.goldenMeanAdjacency) ∧
      (∀ a b : ℤ,
        (a • (1 : Matrix (Fin 2) (Fin 2) ℤ) + b • Graph.goldenMeanAdjacency).det =
          a ^ 2 + a * b - b ^ 2) ∧
      (∀ a b : ℤ,
        ((a ^ 2 + a * b - b ^ 2 : ℤ) : ZMod 5) =
          ((a + 3 * b : ℤ) : ZMod 5) ^ 2) ∧
      (∀ p : ℕ, Nat.Prime p → p ≠ 5 → ∀ y : ZMod p,
        ∃ a b : ZMod p, a ^ 2 + a * b - b ^ 2 = y) := by
  refine ⟨pom_centralizer_det_norm_mod5_centralizer_unique, centralizer_det_formula, ?_, ?_⟩
  · intro a b
    rw [← Int.cast_pow]
    exact (ZMod.intCast_eq_intCast_iff' _ _ 5).2 (det_mod5_is_square a b)
  · intro p hp hp_ne_five y
    by_cases hp_two : p = 2
    · subst p
      fin_cases y <;>
        first
        | exact ⟨0, 0, by decide⟩
        | exact ⟨1, 0, by decide⟩
    · letI : Fact p.Prime := ⟨hp⟩
      classical
      let f : (ZMod p)[X] := X ^ 2 - C (4 * y)
      let g : (ZMod p)[X] := -(C (5 : ZMod p) * X ^ 2)
      have hf2 : degree f = 2 := by
        dsimp [f]
        compute_degree
        · norm_num
        · native_decide
      have hfive_ne_zero : (5 : ZMod p) ≠ 0 := by
        intro h
        have hdiv : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp h
        have hp_eq : p = 5 :=
          (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp hdiv
        exact hp_ne_five hp_eq
      have hg2 : degree g = 2 := by
        dsimp [g]
        compute_degree
        · norm_num
          exact ⟨by native_decide, hfive_ne_zero⟩
      have hodd : Fintype.card (ZMod p) % 2 = 1 := by
        rw [ZMod.card]
        exact (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr hp_two
      obtain ⟨x, b, hxb⟩ :=
        FiniteField.exists_root_sum_quadratic (R := ZMod p) hf2 hg2 hodd
      refine ⟨(x - b) / 2, b, ?_⟩
      dsimp [f, g] at hxb
      simp only [eval_pow, eval_X, eval_neg, eval_sub, eval_C, eval_mul] at hxb
      have htwo_ne_zero : (2 : ZMod p) ≠ 0 := by
        intro h
        have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
        have hp_eq : p = 2 :=
          (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hdiv
        exact hp_two hp_eq
      have hfour_ne_zero : (4 : ZMod p) ≠ 0 := by
        have hfour_eq : (4 : ZMod p) = (2 : ZMod p) ^ 2 := by norm_num
        rw [hfour_eq]
        exact pow_ne_zero 2 htwo_ne_zero
      calc
        ((x - b) / 2) ^ 2 + ((x - b) / 2) * b - b ^ 2 =
            (x ^ 2 - 5 * b ^ 2) / 4 := by
          field_simp [htwo_ne_zero, hfour_ne_zero]
          ring
        _ = y := by
          have hx : x ^ 2 = 4 * y + 5 * b ^ 2 :=
            sub_eq_zero.mp (by
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hxb)
          rw [hx]
          field_simp [hfour_ne_zero]
          ring

end Omega.POM.CentralizerDetMod5
