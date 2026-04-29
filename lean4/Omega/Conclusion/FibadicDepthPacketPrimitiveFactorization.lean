import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-fibadic-depth-packet-primitive-factorization`. -/
theorem paper_conclusion_fibadic_depth_packet_primitive_factorization
    (F : ℕ → ℕ) (Pi : ℕ → Polynomial ℤ)
    (hfactor : ∀ d,
      Polynomial.X ^ F d - 1 =
        ∏ e ∈ (Finset.range (d + 1)).filter (fun e => e ∣ d), Pi e)
    (hPi1 : Pi 1 = Polynomial.X - 1) :
    ∀ d, 2 ≤ d →
      (Polynomial.X - 1) *
          (∏ e ∈ (Finset.range (d + 1)).filter (fun e => e ∣ d ∧ 1 < e), Pi e) =
        Polynomial.X ^ F d - 1 := by
  intro d hd
  let S : Finset ℕ := (Finset.range (d + 1)).filter (fun e => e ∣ d)
  have h1S : 1 ∈ S := by
    simp [S]
    omega
  have herase :
      S.erase 1 = S.filter (fun e => 1 < e) := by
    ext e
    constructor
    · intro he
      have heS : e ∈ S := (Finset.mem_erase.mp he).2
      have hne : e ≠ 1 := (Finset.mem_erase.mp he).1
      have hdiv : e ∣ d := (Finset.mem_filter.mp heS).2
      have hpos : 0 < e := by
        by_contra hnot
        have he0 : e = 0 := Nat.eq_zero_of_not_pos hnot
        subst e
        rcases hdiv with ⟨k, hk⟩
        omega
      exact Finset.mem_filter.mpr ⟨heS, by omega⟩
    · intro he
      have heS : e ∈ S := (Finset.mem_filter.mp he).1
      have hgt : 1 < e := (Finset.mem_filter.mp he).2
      exact Finset.mem_erase.mpr ⟨by omega, heS⟩
  have hfilter :
      S.filter (fun e => 1 < e) =
        (Finset.range (d + 1)).filter (fun e => e ∣ d ∧ 1 < e) := by
    ext e
    simp [S, and_left_comm, and_assoc]
  have hprod :
      Pi 1 *
          (∏ e ∈ (Finset.range (d + 1)).filter (fun e => e ∣ d ∧ 1 < e), Pi e) =
        ∏ e ∈ (Finset.range (d + 1)).filter (fun e => e ∣ d), Pi e := by
    calc
      Pi 1 *
          (∏ e ∈ (Finset.range (d + 1)).filter (fun e => e ∣ d ∧ 1 < e), Pi e) =
          Pi 1 * ∏ e ∈ S.erase 1, Pi e := by
            rw [herase, hfilter]
      _ = ∏ e ∈ S, Pi e := by
            simpa [S, mul_comm] using
              (Finset.prod_erase_mul (s := S) (f := Pi) h1S)
  rw [hfactor d, ← hPi1]
  exact hprod

end Omega.Conclusion
