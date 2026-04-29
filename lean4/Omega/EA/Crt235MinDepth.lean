import Omega.Core.Fib
import Mathlib.Tactic

namespace Omega.EA

/-- Paper label: `prop:crt-235-min-depth`. -/
theorem paper_crt_235_min_depth (m : ℕ) :
    (30 ∣ Nat.fib (m + 2) ↔ 60 ∣ m + 2) ∧
      (((30 ∣ Nat.fib (m + 2)) ∧
          ∀ k : ℕ, 30 ∣ Nat.fib (k + 2) → m ≤ k) ↔ m = 58) := by
  have h30_iff : ∀ n : ℕ, 30 ∣ Nat.fib n ↔ 60 ∣ n := by
    intro n
    constructor
    · intro h30
      have h2 : 2 ∣ Nat.fib n := dvd_trans ⟨15, by omega⟩ h30
      have h3 : 3 ∣ Nat.fib n := dvd_trans ⟨10, by omega⟩ h30
      have h5 : 5 ∣ Nat.fib n := dvd_trans ⟨6, by omega⟩ h30
      have hn3 : 3 ∣ n := (Omega.fib_even_iff_three_dvd n).mp h2
      have hn4 : 4 ∣ n := (Omega.fib_div_three_iff n).mp h3
      have hn5 : 5 ∣ n := (Omega.fib_five_dvd_iff n).mp h5
      have h12 : 12 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) hn3 hn4
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h12 hn5
    · intro h60
      have hn3 : 3 ∣ n := dvd_trans ⟨20, by omega⟩ h60
      have hn4 : 4 ∣ n := dvd_trans ⟨15, by omega⟩ h60
      have hn5 : 5 ∣ n := dvd_trans ⟨12, by omega⟩ h60
      have h2 : 2 ∣ Nat.fib n := (Omega.fib_even_iff_three_dvd n).mpr hn3
      have h3 : 3 ∣ Nat.fib n := (Omega.fib_div_three_iff n).mpr hn4
      have h5 : 5 ∣ Nat.fib n := (Omega.fib_five_dvd_iff n).mpr hn5
      have h6 : 6 ∣ Nat.fib n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h2 h3
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h6 h5
  constructor
  · exact h30_iff (m + 2)
  · constructor
    · rintro ⟨hm30, hmin⟩
      have hm60 : 60 ∣ m + 2 := (h30_iff (m + 2)).mp hm30
      have h58_30 : 30 ∣ Nat.fib (58 + 2) := (h30_iff (58 + 2)).mpr ⟨1, by omega⟩
      have hm_le_58 : m ≤ 58 := hmin 58 h58_30
      rcases hm60 with ⟨t, ht⟩
      have htpos : 0 < t := by
        by_contra h
        have : t = 0 := by omega
        omega
      have h58_le_m : 58 ≤ m := by
        have : 60 ≤ m + 2 := by nlinarith
        omega
      omega
    · intro hm
      subst hm
      constructor
      · exact (h30_iff (58 + 2)).mpr ⟨1, by omega⟩
      · intro k hk
        have hk60 : 60 ∣ k + 2 := (h30_iff (k + 2)).mp hk
        rcases hk60 with ⟨t, ht⟩
        have htpos : 0 < t := by
          by_contra h
          have : t = 0 := by omega
          omega
        have : 60 ≤ k + 2 := by nlinarith
        omega

end Omega.EA
