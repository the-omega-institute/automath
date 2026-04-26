import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.POM

lemma pom_fiber_multiplicity_v2_thresholds_fib_add_three_mod_two (n : Nat) :
    Nat.fib (n + 3) % 2 = Nat.fib n % 2 := by
  have hfib : Nat.fib (n + 3) = Nat.fib n + 2 * Nat.fib (n + 1) := by
    calc
      Nat.fib (n + 3) = Nat.fib ((n + 1) + 2) := rfl
      _ = Nat.fib (n + 1) + Nat.fib ((n + 1) + 1) := Nat.fib_add_two
      _ = Nat.fib (n + 1) + (Nat.fib n + Nat.fib (n + 1)) := by
        rw [show (n + 1) + 1 = n + 2 by omega, Nat.fib_add_two]
      _ = Nat.fib n + 2 * Nat.fib (n + 1) := by ring
  rw [hfib]
  simp [Nat.add_mod]

lemma pom_fiber_multiplicity_v2_thresholds_fib_add_two_odd_iff (ell : Nat) :
    Odd (Nat.fib (ell + 2)) ↔ ell % 3 ≠ 1 := by
  induction ell using Nat.strong_induction_on with
  | h ell ih =>
      by_cases hlt : ell < 3
      · interval_cases ell <;> norm_num [Nat.fib_add_two]
      · have hprev : ell - 3 < ell := by omega
        have hperiod :
            Odd (Nat.fib (ell + 2)) ↔ Odd (Nat.fib ((ell - 3) + 2)) := by
          have hmod :=
            pom_fiber_multiplicity_v2_thresholds_fib_add_three_mod_two ((ell - 3) + 2)
          have hell : ell + 2 = (ell - 3) + 2 + 3 := by omega
          rw [Nat.odd_iff, Nat.odd_iff, hell]
          exact ⟨fun h => by rwa [hmod] at h, fun h => by rwa [hmod]⟩
        have hmod_ell : ell % 3 = (ell - 3) % 3 := by
          have hell : ell % 3 = ((ell - 3) + 3) % 3 := by
            conv_lhs => rw [show ell = (ell - 3) + 3 by omega]
          calc
            ell % 3 = ((ell - 3) + 3) % 3 := hell
            _ = (ell - 3) % 3 := by simp
        rw [hperiod, ih (ell - 3) hprev, hmod_ell]

lemma pom_fiber_multiplicity_v2_thresholds_fib_ne_zero (ell : Nat) :
    Nat.fib (ell + 2) ≠ 0 := by
  intro h
  have hzero : ell + 2 = 0 := Nat.fib_eq_zero.mp h
  omega

lemma pom_fiber_multiplicity_v2_thresholds_factorization_prod (lengths : List Nat) :
    ((lengths.map fun ell => Nat.fib (ell + 2)).prod).factorization 2 =
      (lengths.map fun ell => (Nat.fib (ell + 2)).factorization 2).sum := by
  induction lengths with
  | nil => simp
  | cons ell rest ih =>
      have hfib : Nat.fib (ell + 2) ≠ 0 :=
        pom_fiber_multiplicity_v2_thresholds_fib_ne_zero ell
      have hrest : (rest.map fun ell => Nat.fib (ell + 2)).prod ≠ 0 := by
        intro hzero
        rw [List.prod_eq_zero_iff] at hzero
        rcases List.mem_map.mp hzero with ⟨ell, hell, hfib_zero⟩
        exact pom_fiber_multiplicity_v2_thresholds_fib_ne_zero ell hfib_zero
      rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons,
        Nat.factorization_mul hfib hrest]
      simp [ih]

lemma pom_fiber_multiplicity_v2_thresholds_prod_ne_zero (lengths : List Nat) :
    (lengths.map fun ell => Nat.fib (ell + 2)).prod ≠ 0 := by
  intro hzero
  rw [List.prod_eq_zero_iff] at hzero
  rcases List.mem_map.mp hzero with ⟨ell, hell, hfib_zero⟩
  exact pom_fiber_multiplicity_v2_thresholds_fib_ne_zero ell hfib_zero

lemma pom_fiber_multiplicity_v2_thresholds_odd_prod_iff (lengths : List Nat) :
    Odd ((lengths.map fun ell => Nat.fib (ell + 2)).prod) ↔
      ∀ ell ∈ lengths, ell % 3 ≠ 1 := by
  induction lengths with
  | nil => simp
  | cons ell rest ih =>
      simp [List.prod_cons, Nat.odd_mul,
        pom_fiber_multiplicity_v2_thresholds_fib_add_two_odd_iff, ih]

/-- Paper label: `prop:pom-fiber-multiplicity-v2-thresholds`. -/
theorem paper_pom_fiber_multiplicity_v2_thresholds (lengths : List Nat) :
    let d := (lengths.map (fun ell => Nat.fib (ell + 2))).prod
    d.factorization 2 =
        (lengths.map (fun ell => (Nat.fib (ell + 2)).factorization 2)).sum ∧
      (Odd d ↔ ∀ ell ∈ lengths, ell % 3 ≠ 1) ∧
      (4 ∣ d ↔ 2 ≤ (lengths.map (fun ell => (Nat.fib (ell + 2)).factorization 2)).sum) ∧
      (∀ k : Nat,
        2 ^ k ∣ d ↔
          k ≤ (lengths.map (fun ell => (Nat.fib (ell + 2)).factorization 2)).sum) := by
  dsimp only
  let d := (lengths.map fun ell => Nat.fib (ell + 2)).prod
  let s := (lengths.map fun ell => (Nat.fib (ell + 2)).factorization 2).sum
  have hd : d ≠ 0 := pom_fiber_multiplicity_v2_thresholds_prod_ne_zero lengths
  have hfac : d.factorization 2 = s :=
    pom_fiber_multiplicity_v2_thresholds_factorization_prod lengths
  have hpow : ∀ k : Nat, 2 ^ k ∣ d ↔ k ≤ s := by
    intro k
    simpa [hfac] using (Nat.prime_two.pow_dvd_iff_le_factorization (k := k) (n := d) hd)
  refine ⟨hfac, ?_, ?_, hpow⟩
  · exact pom_fiber_multiplicity_v2_thresholds_odd_prod_iff lengths
  · simpa using hpow 2

end Omega.POM
