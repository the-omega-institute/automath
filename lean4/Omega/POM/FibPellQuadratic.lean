import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.POM.FibPellQuadratic

open Nat

/-- The Pell quadratic form used in the Fibonacci characterization. -/
def pom_fib_pell_quadratic_characterization_form (u v : ℤ) : ℤ :=
  v ^ 2 - u * v - u ^ 2

lemma pom_fib_pell_quadratic_characterization_form_step (u v : ℕ) (_huv : u ≤ v) :
    pom_fib_pell_quadratic_characterization_form (v - u : ℤ) (u : ℤ) =
      -pom_fib_pell_quadratic_characterization_form (u : ℤ) (v : ℤ) := by
  rw [pom_fib_pell_quadratic_characterization_form,
    pom_fib_pell_quadratic_characterization_form]
  ring

lemma pom_fib_pell_quadratic_characterization_pow_neg_one (k : ℕ) :
    (-1 : ℤ) ^ k = 1 ∨ (-1 : ℤ) ^ k = -1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rcases ih with h | h
      · right
        rw [pow_succ, h]
        norm_num
      · left
        rw [pow_succ, h]
        norm_num

theorem pom_fib_pell_quadratic_characterization_inverse
    (u v : ℕ) (hu : 0 < u) (hcop : Nat.Coprime u v) (huv : u < v)
    (hPell :
      pom_fib_pell_quadratic_characterization_form (u : ℤ) (v : ℤ) = 1 ∨
        pom_fib_pell_quadratic_characterization_form (u : ℤ) (v : ℤ) = -1) :
    ∃ k : ℕ, 1 ≤ k ∧ u = Nat.fib k ∧ v = Nat.fib (k + 1) := by
  revert v hu hcop huv hPell
  refine Nat.strong_induction_on u ?_
  intro u ih v hu hcop huv hPell
  by_cases hu_one : u = 1
  · subst u
    have hv_le_two : v ≤ 2 := by
      by_contra hv_not
      have hv_three : 3 ≤ v := by omega
      have hv_three_int : (3 : ℤ) ≤ (v : ℤ) := by exact_mod_cast hv_three
      have hQ_ge :
          5 ≤ pom_fib_pell_quadratic_characterization_form (1 : ℤ) (v : ℤ) := by
        rw [pom_fib_pell_quadratic_characterization_form]
        nlinarith [sq_nonneg ((v : ℤ) - 3)]
      rcases hPell with hPell | hPell
      · have hPell' :
            pom_fib_pell_quadratic_characterization_form (1 : ℤ) (v : ℤ) = 1 := by
          simpa using hPell
        nlinarith
      · have hPell' :
            pom_fib_pell_quadratic_characterization_form (1 : ℤ) (v : ℤ) = -1 := by
          simpa using hPell
        nlinarith
    have hv_two : v = 2 := by omega
    subst v
    exact ⟨2, by native_decide⟩
  · have hu_two : 2 ≤ u := by omega
    let w : ℕ := v - u
    have hw_pos : 0 < w := Nat.sub_pos_of_lt huv
    have hv_eq_add : u + w = v := Nat.add_sub_of_le huv.le
    have hQ_rewrite :
        pom_fib_pell_quadratic_characterization_form (u : ℤ) (v : ℤ) =
          (w : ℤ) ^ 2 + (u : ℤ) * (w : ℤ) - (u : ℤ) ^ 2 := by
      rw [pom_fib_pell_quadratic_characterization_form]
      have hv_cast : (v : ℤ) = (u : ℤ) + (w : ℤ) := by exact_mod_cast hv_eq_add.symm
      rw [hv_cast]
      ring
    have hw_lt : w < u := by
      by_contra hw_not_lt
      have huw : u ≤ w := by omega
      have huw_int : (u : ℤ) ≤ (w : ℤ) := by exact_mod_cast huw
      have hu_nonneg_int : 0 ≤ (u : ℤ) := by exact_mod_cast Nat.zero_le u
      have hu_two_int : (2 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu_two
      have hsq : (u : ℤ) ^ 2 ≤ (w : ℤ) ^ 2 :=
        (sq_le_sq₀ hu_nonneg_int (hu_nonneg_int.trans huw_int)).mpr huw_int
      have hprod : (u : ℤ) ^ 2 ≤ (u : ℤ) * (w : ℤ) := by
        simpa [pow_two] using mul_le_mul_of_nonneg_left huw_int hu_nonneg_int
      have hQ_ge :
          4 ≤ pom_fib_pell_quadratic_characterization_form (u : ℤ) (v : ℤ) := by
        rw [hQ_rewrite]
        nlinarith
      rcases hPell with hPell | hPell <;> nlinarith
    have hcop_uw : Nat.Coprime u w := by
      rw [← hv_eq_add] at hcop
      exact Nat.coprime_self_add_right.mp hcop
    have hPred :
        pom_fib_pell_quadratic_characterization_form (w : ℤ) (u : ℤ) = 1 ∨
          pom_fib_pell_quadratic_characterization_form (w : ℤ) (u : ℤ) = -1 := by
      have hstep :=
        pom_fib_pell_quadratic_characterization_form_step u v huv.le
      rw [show w = v - u from rfl]
      rw [Nat.cast_sub huv.le]
      rw [hstep]
      rcases hPell with hPell | hPell
      · right
        rw [hPell]
      · left
        rw [hPell]
        norm_num
    rcases ih w hw_lt u hw_pos hcop_uw.symm hw_lt hPred with ⟨k, hk, hw, hu_fib⟩
    refine ⟨k + 1, by omega, hu_fib, ?_⟩
    calc
      v = u + w := hv_eq_add.symm
      _ = Nat.fib (k + 1) + Nat.fib k := by rw [hu_fib, hw]
      _ = Nat.fib (k + 1 + 1) := by
            rw [add_comm]
            exact (Nat.fib_add_two (n := k)).symm

/-- Full paper-facing characterization of coprime positive Pell solutions by consecutive
Fibonacci numbers.
    prop:pom-fib-pell-quadratic-characterization -/
theorem paper_pom_fib_pell_quadratic_characterization
    (u v : ℕ) (hu : 0 < u) (hcop : Nat.Coprime u v) (huv : u < v) :
    ((∃ k : ℕ, 1 ≤ k ∧ u = Nat.fib k ∧ v = Nat.fib (k + 1)) ↔
      ((v : ℤ)^2 - (u : ℤ) * (v : ℤ) - (u : ℤ)^2 = 1 ∨
        (v : ℤ)^2 - (u : ℤ) * (v : ℤ) - (u : ℤ)^2 = -1)) := by
  constructor
  · rintro ⟨k, hk, rfl, rfl⟩
    have h := Omega.fib_pell_quadratic k hk
    have hsign := pom_fib_pell_quadratic_characterization_pow_neg_one k
    rcases hsign with hsign | hsign
    · left
      simpa [hsign, mul_comm] using h
    · right
      simpa [hsign, mul_comm] using h
  · intro h
    exact pom_fib_pell_quadratic_characterization_inverse u v hu hcop huv h

/-- Fibonacci Pell quadratic form (even): F_{2k+1}² = F_{2k}·F_{2k+1} + F_{2k}² + 1.
    Derived from Cassini even: F_{2k}·F_{2k+2} + 1 = F_{2k+1}² with F_{2k+2} = F_{2k+1} + F_{2k}.
    prop:pom-fib-pell-quadratic-characterization -/
theorem fib_pell_even (k : ℕ) :
    Nat.fib (2 * k + 1) ^ 2 =
      Nat.fib (2 * k) * Nat.fib (2 * k + 1) + Nat.fib (2 * k) ^ 2 + 1 := by
  have hcas := Omega.fib_cassini_even_indexed k
  -- hcas : F(2k+1)^2 = F(2k) * F(2k+2) + 1
  have hrec : Nat.fib (2 * k + 2) = Nat.fib (2 * k) + Nat.fib (2 * k + 1) := Nat.fib_add_two
  nlinarith [sq_nonneg (Nat.fib (2 * k))]

/-- Fibonacci Pell quadratic form (odd): F_{2k+2}² + 1 = F_{2k+1}·F_{2k+2} + F_{2k+1}².
    Derived from Cassini odd: F_{2k+1}·F_{2k+3} = F_{2k+2}² + 1 with F_{2k+3} = F_{2k+2} + F_{2k+1}.
    prop:pom-fib-pell-quadratic-characterization -/
theorem fib_pell_odd (k : ℕ) :
    Nat.fib (2 * k + 2) ^ 2 + 1 =
      Nat.fib (2 * k + 1) * Nat.fib (2 * k + 2) + Nat.fib (2 * k + 1) ^ 2 := by
  have hcas := Omega.fib_cassini_odd_indexed k
  -- hcas : F(2k+2)^2 + 1 = F(2k+1) * F(2k+3)
  have hrec : Nat.fib (2 * k + 3) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) := Nat.fib_add_two
  nlinarith [sq_nonneg (Nat.fib (2 * k + 1))]

/-- Paper seeds: Pell quadratic at small indices.
    prop:pom-fib-pell-quadratic-characterization -/
theorem paper_pom_fib_pell_quadratic :
    Nat.fib 1 ^ 2 = Nat.fib 0 * Nat.fib 1 + Nat.fib 0 ^ 2 + 1 ∧
    Nat.fib 2 ^ 2 + 1 = Nat.fib 1 * Nat.fib 2 + Nat.fib 1 ^ 2 ∧
    Nat.fib 3 ^ 2 = Nat.fib 2 * Nat.fib 3 + Nat.fib 2 ^ 2 + 1 ∧
    Nat.fib 4 ^ 2 + 1 = Nat.fib 3 * Nat.fib 4 + Nat.fib 3 ^ 2 := by
  native_decide

/-- Paper-facing golden-ratio certificate: the Fibonacci convergents have exact error
`(-1)^k * φ⁻ᵏ`, and the associated Pell norm is `(-1)^k`. -/
theorem paper_pom_zphi_unit_certificate_error (k : ℕ) :
    (((Nat.fib (k + 1) : ℝ) - (Nat.fib k : ℝ) * Real.goldenRatio =
        (-1 : ℝ) ^ k * (Real.goldenRatio⁻¹) ^ k) ∧
      ((Nat.fib (k + 1) : ℝ) ^ 2 - (Nat.fib (k + 1) : ℝ) * (Nat.fib k : ℝ) -
          (Nat.fib k : ℝ) ^ 2 = (-1 : ℝ) ^ k)) := by
  refine ⟨?_, ?_⟩
  · calc
      (Nat.fib (k + 1) : ℝ) - (Nat.fib k : ℝ) * Real.goldenRatio
          = Real.goldenConj ^ k := by
              simpa [mul_comm] using Real.fib_succ_sub_goldenRatio_mul_fib k
      _ = (-1 : ℝ) ^ k * (Real.goldenRatio⁻¹) ^ k := by
            rw [show Real.goldenConj = -(Real.goldenRatio⁻¹) by
              nlinarith [Real.inv_goldenRatio]]
            rw [neg_eq_neg_one_mul, mul_pow]
  · cases k with
    | zero =>
        norm_num
    | succ k =>
        exact_mod_cast Omega.fib_pell_quadratic (k + 1) (by omega)

end Omega.POM.FibPellQuadratic
