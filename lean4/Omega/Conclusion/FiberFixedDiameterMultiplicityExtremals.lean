import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

private theorem conclusion_fiber_fixed_diameter_multiplicity_extremals_fib_shifted_fusion_nat
    (a b : ℕ) :
    Nat.fib (a + 2) * Nat.fib (b + 2) =
      Nat.fib (a + b + 2) + Nat.fib a * Nat.fib b := by
  have hadd := Nat.fib_add (a + 1) b
  rw [show a + 1 + b + 1 = a + b + 2 by omega, show a + 1 + 1 = a + 2 by omega] at hadd
  have hb := Nat.fib_add_two (n := b)
  have ha := Nat.fib_add_two (n := a)
  rw [hb, Nat.mul_add, hadd, ha]
  ring

private theorem conclusion_fiber_fixed_diameter_multiplicity_extremals_fib_shifted_le
    (a b : ℕ) :
    Nat.fib (a + b + 2) ≤ Nat.fib (a + 2) * Nat.fib (b + 2) := by
  have h :=
    conclusion_fiber_fixed_diameter_multiplicity_extremals_fib_shifted_fusion_nat a b
  omega

private theorem conclusion_fiber_fixed_diameter_multiplicity_extremals_fib_le_two_pow :
    ∀ m : ℕ, Nat.fib (m + 2) ≤ 2 ^ m
  | 0 => by simp
  | 1 => by simp [Nat.fib]
  | m + 2 => by
      have h1 := conclusion_fiber_fixed_diameter_multiplicity_extremals_fib_le_two_pow (m + 1)
      have h2 := conclusion_fiber_fixed_diameter_multiplicity_extremals_fib_le_two_pow m
      have hrec : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (Nat.fib_add_two (n := m + 2))
      calc
        Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := hrec
        _ ≤ 2 ^ m + 2 ^ (m + 1) := Nat.add_le_add h2 h1
        _ ≤ 2 ^ (m + 1) + 2 ^ (m + 1) :=
          Nat.add_le_add_right (Nat.pow_le_pow_right (by omega) (by omega)) _
        _ = 2 ^ (m + 2) := by ring

private theorem conclusion_fiber_fixed_diameter_multiplicity_extremals_lower :
    ∀ {r : ℕ} (parts : Fin r → ℕ),
      Nat.fib ((∑ i, parts i) + 2) ≤ ∏ i, Nat.fib (parts i + 2)
  | 0, _ => by simp
  | r + 1, parts => by
      rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
      have htail :
          Nat.fib ((∑ i : Fin r, parts i.succ) + 2) ≤
            ∏ i : Fin r, Nat.fib (parts i.succ + 2) :=
        conclusion_fiber_fixed_diameter_multiplicity_extremals_lower (fun i => parts i.succ)
      have hhead :
          Nat.fib (parts 0 + ∑ i : Fin r, parts i.succ + 2) ≤
            Nat.fib (parts 0 + 2) * Nat.fib ((∑ i : Fin r, parts i.succ) + 2) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          conclusion_fiber_fixed_diameter_multiplicity_extremals_fib_shifted_le
            (parts 0) (∑ i : Fin r, parts i.succ)
      exact hhead.trans (Nat.mul_le_mul_left _ htail)

private theorem conclusion_fiber_fixed_diameter_multiplicity_extremals_upper :
    ∀ {r : ℕ} (parts : Fin r → ℕ),
      (∏ i, Nat.fib (parts i + 2)) ≤ 2 ^ (∑ i, parts i)
  | 0, _ => by simp
  | r + 1, parts => by
      rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
      have hhead :
          Nat.fib (parts 0 + 2) ≤ 2 ^ parts 0 :=
        conclusion_fiber_fixed_diameter_multiplicity_extremals_fib_le_two_pow (parts 0)
      have htail :
          (∏ i : Fin r, Nat.fib (parts i.succ + 2)) ≤ 2 ^ (∑ i : Fin r, parts i.succ) :=
        conclusion_fiber_fixed_diameter_multiplicity_extremals_upper (fun i => parts i.succ)
      calc
        Nat.fib (parts 0 + 2) * ∏ i : Fin r, Nat.fib (parts i.succ + 2)
            ≤ 2 ^ parts 0 * 2 ^ (∑ i : Fin r, parts i.succ) :=
          Nat.mul_le_mul hhead htail
        _ = 2 ^ (parts 0 + ∑ i : Fin r, parts i.succ) := (Nat.pow_add 2 _ _).symm

/-- Paper label: `thm:conclusion-fiber-fixed-diameter-multiplicity-extremals`. For a fixed
diameter `D`, the product of the shifted Fibonacci multiplicities over any `r`-part decomposition
of `D` lies between the single-block value `F_{D+2}` and the fully split value `2^D`. -/
theorem paper_conclusion_fiber_fixed_diameter_multiplicity_extremals
    (D r : ℕ) (parts : Fin r → ℕ) (hpos : ∀ i, 1 ≤ parts i)
    (hsum : (Finset.univ.sum fun i : Fin r => parts i) = D) :
    Nat.fib (D + 2) ≤ Finset.univ.prod (fun i : Fin r => Nat.fib (parts i + 2)) ∧
      Finset.univ.prod (fun i : Fin r => Nat.fib (parts i + 2)) ≤ 2 ^ D := by
  let _ := hpos
  constructor
  · simpa [hsum] using conclusion_fiber_fixed_diameter_multiplicity_extremals_lower parts
  · simpa [hsum] using conclusion_fiber_fixed_diameter_multiplicity_extremals_upper parts

end Omega.Conclusion
