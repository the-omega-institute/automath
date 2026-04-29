import Mathlib.Tactic
import Omega.POM.FiberZxMinusOnePsi3Sign
import Omega.POM.ToggleScanSignEdgeParity

namespace Omega.POM

open Omega.POM.FibCubeEdgeParity

private theorem pom_witten_index_scan_sign_coupling_odd_fiber_fibConvSum_mod_two
    (ℓ : ℕ) :
    fibConvSum ℓ % 2 = if ℓ % 6 = 1 ∨ ℓ % 6 = 3 then 1 else 0 := by
  induction ℓ using Nat.strong_induction_on with
  | h n ih =>
      by_cases hsmall : n < 3
      · interval_cases n <;> native_decide
      · have hrec :
            fibConvSum n = fibConvSum (n - 1) + fibConvSum (n - 2) + Nat.fib n := by
          have h := fibConvSum_recurrence (n - 2) (by omega)
          simpa [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega] using h
        have hn1 := ih (n - 1) (by omega)
        have hn2 := ih (n - 2) (by omega)
        rw [hrec]
        rw [show
          (fibConvSum (n - 1) + fibConvSum (n - 2) + Nat.fib n) % 2 =
            ((fibConvSum (n - 1) % 2 + fibConvSum (n - 2) % 2) % 2 +
              Nat.fib n % 2) % 2 by simp [Nat.add_mod]]
        rw [hn1, hn2, Omega.fib_mod_two_period n]
        have hlt : n % 6 < 6 := Nat.mod_lt n (by omega)
        interval_cases h : n % 6
        · have hn1mod : (n - 1) % 6 = 5 := by omega
          have hn2mod : (n - 2) % 6 = 4 := by omega
          have hn3mod : n % 3 = 0 := by omega
          simp [hn1mod, hn2mod, hn3mod]
        · have hn1mod : (n - 1) % 6 = 0 := by omega
          have hn2mod : (n - 2) % 6 = 5 := by omega
          have hn3mod : n % 3 = 1 := by omega
          simp [hn1mod, hn2mod, hn3mod]
        · have hn1mod : (n - 1) % 6 = 1 := by omega
          have hn2mod : (n - 2) % 6 = 0 := by omega
          have hn3mod : n % 3 = 2 := by omega
          simp [hn1mod, hn2mod, hn3mod]
        · have hn1mod : (n - 1) % 6 = 2 := by omega
          have hn2mod : (n - 2) % 6 = 1 := by omega
          have hn3mod : n % 3 = 0 := by omega
          simp [hn1mod, hn2mod, hn3mod]
        · have hn1mod : (n - 1) % 6 = 3 := by omega
          have hn2mod : (n - 2) % 6 = 2 := by omega
          have hn3mod : n % 3 = 1 := by omega
          simp [hn1mod, hn2mod, hn3mod]
        · have hn1mod : (n - 1) % 6 = 4 := by omega
          have hn2mod : (n - 2) % 6 = 3 := by omega
          have hn3mod : n % 3 = 2 := by omega
          simp [hn1mod, hn2mod, hn3mod]

private theorem pom_witten_index_scan_sign_coupling_odd_fiber_pow_neg_one_mod_two
    {a b : ℕ} (h : a % 2 = b % 2) : (-1 : ℤ) ^ a = (-1 : ℤ) ^ b := by
  calc
    (-1 : ℤ) ^ a = (-1 : ℤ) ^ (a % 2 + 2 * (a / 2)) := by
      rw [Nat.mod_add_div a 2]
    _ = (-1 : ℤ) ^ (a % 2) := by
      simp [pow_add, pow_mul]
    _ = (-1 : ℤ) ^ (b % 2) := by
      rw [h]
    _ = (-1 : ℤ) ^ (b % 2 + 2 * (b / 2)) := by
      simp [pow_add, pow_mul]
    _ = (-1 : ℤ) ^ b := by
      rw [Nat.mod_add_div b 2]

private theorem pom_witten_index_scan_sign_coupling_odd_fiber_sign_eq_pow
    (n : ℕ) : (if n % 2 = 0 then (1 : ℤ) else -1) = (-1 : ℤ) ^ n := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have hp :
        (-1 : ℤ) ^ n = (-1 : ℤ) ^ (0 : ℕ) :=
      pom_witten_index_scan_sign_coupling_odd_fiber_pow_neg_one_mod_two (by simpa using h)
    simpa [h] using hp.symm
  · have hp :
        (-1 : ℤ) ^ n = (-1 : ℤ) ^ (1 : ℕ) :=
      pom_witten_index_scan_sign_coupling_odd_fiber_pow_neg_one_mod_two (by simpa using h)
    simpa [h] using hp.symm

private theorem pom_witten_index_scan_sign_coupling_odd_fiber_no_exceptional
    {lengths : List ℕ} (hOdd : toggleScanFiberVertexCount lengths % 2 = 1) :
    ∀ ℓ ∈ lengths, ℓ % 3 ≠ 1 := by
  rw [toggleScanFiberVertexCount] at hOdd
  exact (paper_pom_fiber_parity_mod3 lengths).mp hOdd

private theorem pom_witten_index_scan_sign_coupling_odd_fiber_exceptional_nil_of_no
    (lengths : List ℕ) (hNo : ∀ ℓ ∈ lengths, ℓ % 3 ≠ 1) :
    toggleScanExceptionalLengths lengths = [] := by
  induction lengths with
  | nil =>
      simp [toggleScanExceptionalLengths]
  | cons a lengths ih =>
      have ha : a % 3 ≠ 1 := hNo a (by simp)
      have htail : ∀ ℓ ∈ lengths, ℓ % 3 ≠ 1 := by
        intro ℓ hℓ
        exact hNo ℓ (by simp [hℓ])
      simpa [toggleScanExceptionalLengths, ha] using ih htail

private theorem pom_witten_index_scan_sign_coupling_odd_fiber_exceptional_nil
    {lengths : List ℕ} (hOdd : toggleScanFiberVertexCount lengths % 2 = 1) :
    toggleScanExceptionalLengths lengths = [] := by
  have hNo := pom_witten_index_scan_sign_coupling_odd_fiber_no_exceptional hOdd
  exact pom_witten_index_scan_sign_coupling_odd_fiber_exceptional_nil_of_no lengths hNo

private theorem pom_witten_index_scan_sign_coupling_odd_fiber_exponent_parity
    (lengths : List ℕ) (hNo : ∀ ℓ ∈ lengths, ℓ % 3 ≠ 1) :
    (lengths.map fun ℓ => (ℓ + 1) / 3).sum % 2 =
      ((lengths.map fun ℓ => fibConvSum ℓ % 2).sum +
        (lengths.filter fun ℓ => ℓ % 6 = 2).length) % 2 := by
  induction lengths with
  | nil =>
      simp
  | cons a lengths ih =>
      have haNo : a % 3 ≠ 1 := hNo a (by simp)
      have htail : ∀ ℓ ∈ lengths, ℓ % 3 ≠ 1 := by
        intro ℓ hℓ
        exact hNo ℓ (by simp [hℓ])
      have hih := ih htail
      have hfib := pom_witten_index_scan_sign_coupling_odd_fiber_fibConvSum_mod_two a
      have hcases :
          a % 6 = 0 ∨ a % 6 = 1 ∨ a % 6 = 2 ∨
            a % 6 = 3 ∨ a % 6 = 4 ∨ a % 6 = 5 := by
        omega
      rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
      · have hdiv : ((a + 1) / 3) % 2 = 0 := by omega
        simp [List.filter, h0, hfib, hdiv, hih, Nat.add_mod]
      · exact False.elim (haNo (by omega))
      · have hdiv : ((a + 1) / 3) % 2 = 1 := by omega
        simp [List.filter, h2, hfib, hdiv, hih, Nat.add_mod]
        omega
      · have hdiv : ((a + 1) / 3) % 2 = 1 := by omega
        simp [List.filter, h3, hfib, hdiv, hih, Nat.add_mod]
        omega
      · exact False.elim (haNo (by omega))
      · have hdiv : ((a + 1) / 3) % 2 = 0 := by omega
        simp [List.filter, h5, hfib, hdiv, hih, Nat.add_mod]

/-- Paper label: `prop:pom-witten-index-scan-sign-coupling-odd-fiber`. -/
theorem paper_pom_witten_index_scan_sign_coupling_odd_fiber (lengths : List ℕ)
    (hOdd : toggleScanFiberVertexCount lengths % 2 = 1) :
    (lengths.map pathIndSetPolyNegOne).prod =
      toggleScanGeneralFiberSign lengths *
        (-1 : ℤ) ^ ((lengths.filter fun ℓ => ℓ % 6 = 2).length) := by
  have hNo := pom_witten_index_scan_sign_coupling_odd_fiber_no_exceptional hOdd
  have hExceptional :
      toggleScanExceptionalLengths lengths = [] :=
    pom_witten_index_scan_sign_coupling_odd_fiber_exceptional_nil hOdd
  have hprod_ne : (lengths.map pathIndSetPolyNegOne).prod ≠ 0 := by
    intro hzero
    rcases (paper_pom_fiber_signed_index_mod3 lengths).mp hzero with ⟨ℓ, hℓ, hmod⟩
    exact hNo ℓ hℓ hmod
  have hprod :
      (lengths.map pathIndSetPolyNegOne).prod =
        (-1 : ℤ) ^ (lengths.map fun ℓ => (ℓ + 1) / 3).sum :=
    (paper_pom_fiber_zx_minus_one_psi3_sign lengths).2 hprod_ne
  have hsign :
      toggleScanGeneralFiberSign lengths =
        if (lengths.map fun ℓ => fibConvSum ℓ % 2).sum % 2 = 0 then 1 else -1 := by
    exact (paper_pom_toggle_scan_sign_general_fiber lengths).2.2 hExceptional
  have hparity :=
    pom_witten_index_scan_sign_coupling_odd_fiber_exponent_parity lengths hNo
  rw [hprod, hsign]
  rw [pom_witten_index_scan_sign_coupling_odd_fiber_sign_eq_pow]
  rw [← pow_add]
  exact pom_witten_index_scan_sign_coupling_odd_fiber_pow_neg_one_mod_two hparity

end Omega.POM
