import Mathlib.Tactic

namespace Omega.Zeta

lemma xi_time_part62d_rational_rose_period_petal_classification_mod_two_zero_of_ne_one
    {m : ℕ} (hm : m % 2 ≠ 1) : m % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
  · exact h0
  · exact (hm h1).elim

lemma xi_time_part62d_rational_rose_period_petal_classification_odd_right_of_even_left
    {n d : ℕ} (hcop : Nat.Coprime n d) (hn : n % 2 = 0) : d % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one d with hd | hd
  · have h2n : 2 ∣ n := (Nat.dvd_iff_mod_eq_zero).2 hn
    have h2d : 2 ∣ d := (Nat.dvd_iff_mod_eq_zero).2 hd
    have h2gcd : 2 ∣ Nat.gcd n d := Nat.dvd_gcd h2n h2d
    rw [hcop.gcd_eq_one] at h2gcd
    norm_num at h2gcd
  · exact hd

lemma xi_time_part62d_rational_rose_period_petal_classification_gcd_eq
    (n d : ℕ) (hcop : Nat.Coprime n d) :
    Nat.gcd (d + n) (2 * n) = if n % 2 = 1 ∧ d % 2 = 1 then 2 else 1 := by
  let g := Nat.gcd (d + n) (2 * n)
  have hsumcop : Nat.Coprime (d + n) n := by
    exact (Nat.coprime_add_self_left).2 hcop.symm
  have hgcop : Nat.Coprime g n := by
    exact hsumcop.of_dvd_left (Nat.gcd_dvd_left (d + n) (2 * n))
  have hgdvd2 : g ∣ 2 := by
    exact (hgcop.dvd_mul_right).1 (Nat.gcd_dvd_right (d + n) (2 * n))
  by_cases hnodd : n % 2 = 1
  · by_cases hdodd : d % 2 = 1
    · have hsum0 : (d + n) % 2 = 0 := by
        simp [Nat.add_mod, hdodd, hnodd]
      have h2sum : 2 ∣ d + n := (Nat.dvd_iff_mod_eq_zero).2 hsum0
      have h2g : 2 ∣ g := Nat.dvd_gcd h2sum (dvd_mul_right 2 n)
      have hg : g = 2 := Nat.dvd_antisymm hgdvd2 h2g
      simp [g, hnodd, hdodd, hg]
    · have hd0 :
        d % 2 = 0 :=
        xi_time_part62d_rational_rose_period_petal_classification_mod_two_zero_of_ne_one
          hdodd
      have hnot2g : ¬2 ∣ g := by
        intro h2g
        have h2sum : 2 ∣ d + n :=
          h2g.trans (Nat.gcd_dvd_left (d + n) (2 * n))
        have hsum0 : (d + n) % 2 = 0 := (Nat.dvd_iff_mod_eq_zero).1 h2sum
        have hsum1 : (d + n) % 2 = 1 := by
          simp [Nat.add_mod, hd0, hnodd]
        omega
      have hg : g = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 hgdvd2 with hg | hg
        · exact hg
        · exfalso
          exact hnot2g (by simp [hg])
      simp [g, hnodd, hdodd, hg]
  · have hn0 :
      n % 2 = 0 :=
      xi_time_part62d_rational_rose_period_petal_classification_mod_two_zero_of_ne_one
        hnodd
    have hdodd :
      d % 2 = 1 :=
      xi_time_part62d_rational_rose_period_petal_classification_odd_right_of_even_left
        hcop hn0
    have hnot2g : ¬2 ∣ g := by
      intro h2g
      have h2sum : 2 ∣ d + n :=
        h2g.trans (Nat.gcd_dvd_left (d + n) (2 * n))
      have hsum0 : (d + n) % 2 = 0 := (Nat.dvd_iff_mod_eq_zero).1 h2sum
      have hsum1 : (d + n) % 2 = 1 := by
        simp [Nat.add_mod, hdodd, hn0]
      omega
    have hg : g = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hgdvd2 with hg | hg
      · exact hg
      · exfalso
        exact hnot2g (by simp [hg])
    simp [g, hnodd, hg]

/-- Paper label: `thm:xi-time-part62d-rational-rose-period-petal-classification`. -/
theorem paper_xi_time_part62d_rational_rose_period_petal_classification
    (n d : ℕ) (hn : 0 < n) (_hd : 0 < d) (hcop : Nat.Coprime n d) :
    Nat.gcd (d + n) (2 * n) = (if n % 2 = 1 ∧ d % 2 = 1 then 2 else 1) ∧
      (2 * d) / Nat.gcd (d + n) (2 * n) =
        (if n % 2 = 1 ∧ d % 2 = 1 then d else 2 * d) ∧
      (2 * n) / Nat.gcd (d + n) (2 * n) =
        (if n % 2 = 1 ∧ d % 2 = 1 then n else 2 * n) := by
  have _hn_pos : 0 < n := hn
  have hgcd :=
    xi_time_part62d_rational_rose_period_petal_classification_gcd_eq n d hcop
  constructor
  · exact hgcd
  constructor
  · rw [hgcd]
    by_cases hodd : n % 2 = 1 ∧ d % 2 = 1 <;> simp [hodd]
  · rw [hgcd]
    by_cases hodd : n % 2 = 1 ∧ d % 2 = 1 <;> simp [hodd]

end Omega.Zeta
