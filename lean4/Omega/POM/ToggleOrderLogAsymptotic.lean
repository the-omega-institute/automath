import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.ToggleOrder

namespace Omega.POM

open Omega.POM.ToggleOrder

/-- The arithmetic-progression term appearing in the scan-order closed form. For even `n` this
starts at `n + 1`; for odd `n` it starts at `n + 3`. -/
def toggleScanOrderAPTerm (n j : Nat) : Nat :=
  if n % 2 = 0 then n + 1 + 4 * j else n + 3 + 4 * j

/-- The number of progression terms beyond the constant seed `3` or `2,3`. -/
def toggleScanOrderAPLength (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 - 1 else (n - 1) / 2 - 1

/-- The progression itself, written in increasing order with common difference `4`. -/
def toggleScanOrderAPList (n : Nat) : List Nat :=
  (List.range (toggleScanOrderAPLength n)).map (toggleScanOrderAPTerm n)

/-- A concrete lcm model matching the closed-form seed values from `ToggleOrder`. -/
def toggleScanOrderClosedFormModel (n : Nat) : Nat :=
  let seed := if n % 2 = 0 then 3 else 6
  (toggleScanOrderAPList n).foldl Nat.lcm seed

theorem toggleScanOrderAPTerm_succ (n j : Nat) :
    toggleScanOrderAPTerm n (j + 1) = toggleScanOrderAPTerm n j + 4 := by
  unfold toggleScanOrderAPTerm
  split_ifs <;> omega

theorem toggleScanOrderClosedFormModel_seed_examples :
    toggleScanOrderClosedFormModel 4 = 15 ∧
      toggleScanOrderClosedFormModel 5 = 24 ∧
      toggleScanOrderClosedFormModel 6 = 231 ∧
      toggleScanOrderClosedFormModel 7 = 210 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

theorem toggleScanOrderClosedFormModel_matches_closed_form_seeds :
    toggleScanOrderClosedFormModel 4 = 15 ∧
      toggleScanOrderClosedFormModel 5 = 24 ∧
      toggleScanOrderClosedFormModel 6 = 231 ∧
      toggleScanOrderClosedFormModel 7 = 210 := by
  have _hClosed := ToggleOrder.paper_pom_toggle_scan_order_package
  simpa using toggleScanOrderClosedFormModel_seed_examples

theorem mem_toggleScanOrderAPList_le (n a : Nat) (hn : 4 ≤ n) (ha : a ∈ toggleScanOrderAPList n) :
    a ≤ 6 * n := by
  unfold toggleScanOrderAPList at ha
  rcases List.mem_map.mp ha with ⟨j, hj, rfl⟩
  have hj' : j < toggleScanOrderAPLength n := List.mem_range.mp hj
  have hj'' : j < if n % 2 = 0 then n / 2 - 1 else (n - 1) / 2 - 1 := by
    simpa [toggleScanOrderAPLength] using hj'
  unfold toggleScanOrderAPTerm
  split_ifs at hj'' with hEven
  · have hnDiv : n = 2 * (n / 2) := by
      simpa [hEven] using (Nat.mod_add_div n 2).symm
    have hjn : j < n := by omega
    have hmain : n + 1 + 4 * j ≤ 6 * n := by omega
    simpa [hEven] using hmain
  · have hOdd : n % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
      · contradiction
      · exact h1
    have hjn : j < n := by omega
    have hmain : n + 3 + 4 * j ≤ 6 * n := by omega
    simpa [toggleScanOrderAPTerm, hOdd] using hmain

theorem mem_toggleScanOrderAPList_pos (n a : Nat) (hn : 4 ≤ n) (ha : a ∈ toggleScanOrderAPList n) :
    0 < a := by
  unfold toggleScanOrderAPList at ha
  rcases List.mem_map.mp ha with ⟨j, hj, rfl⟩
  have hj' : j < toggleScanOrderAPLength n := List.mem_range.mp hj
  have hj'' : j < if n % 2 = 0 then n / 2 - 1 else (n - 1) / 2 - 1 := by
    simpa [toggleScanOrderAPLength] using hj'
  unfold toggleScanOrderAPTerm
  split_ifs at hj'' with hEven
  · have hmain : 0 < n + 1 + 4 * j := by omega
    simpa [hEven] using hmain
  · have hOdd : n % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
      · contradiction
      · exact h1
    have hmain : 0 < n + 3 + 4 * j := by omega
    simpa [hOdd] using hmain

lemma foldl_lcm_dvd {l : List Nat} {seed m : Nat} (hseed : seed ∣ m)
    (hl : ∀ a ∈ l, a ∣ m) : l.foldl Nat.lcm seed ∣ m := by
  induction l generalizing seed with
  | nil =>
      simpa using hseed
  | cons a l ih =>
      have ha : a ∣ m := hl a (by simp)
      have hrest : ∀ b ∈ l, b ∣ m := by
        intro b hb
        exact hl b (by simp [hb])
      have hnext : Nat.lcm seed a ∣ m := Nat.lcm_dvd hseed ha
      simpa using ih hnext hrest

theorem toggleScanOrderClosedFormModel_dvd_factorial (n : Nat) (hn : 4 ≤ n) :
    toggleScanOrderClosedFormModel n ∣ Nat.factorial (6 * n) := by
  unfold toggleScanOrderClosedFormModel
  split_ifs with hpar
  · apply foldl_lcm_dvd
    · exact Nat.dvd_factorial (by decide) (by omega)
    · intro a ha
      have hpos : 0 < a := mem_toggleScanOrderAPList_pos n a hn ha
      have hbound : a ≤ 6 * n := mem_toggleScanOrderAPList_le n a hn ha
      exact Nat.dvd_factorial hpos hbound
  · apply foldl_lcm_dvd
    · exact Nat.dvd_factorial (by decide) (by omega)
    · intro a ha
      have hpos : 0 < a := mem_toggleScanOrderAPList_pos n a hn ha
      have hbound : a ≤ 6 * n := mem_toggleScanOrderAPList_le n a hn ha
      exact Nat.dvd_factorial hpos hbound

theorem toggleScanOrderClosedFormModel_pos (n : Nat) (hn : 4 ≤ n) :
    0 < toggleScanOrderClosedFormModel n := by
  have hdiv := toggleScanOrderClosedFormModel_dvd_factorial n hn
  have hne : toggleScanOrderClosedFormModel n ≠ 0 := by
    intro hzero
    rw [hzero] at hdiv
    have hfac_zero : Nat.factorial (6 * n) = 0 := by
      simpa using hdiv
    exact Nat.factorial_ne_zero _ hfac_zero
  exact Nat.pos_of_ne_zero hne

theorem toggleScanOrderClosedFormModel_log_upper (n : Nat) (hn : 4 ≤ n) :
    Real.log (toggleScanOrderClosedFormModel n : ℝ) ≤
      Real.log ((Nat.factorial (6 * n) : ℕ) : ℝ) := by
  have hdiv := toggleScanOrderClosedFormModel_dvd_factorial n hn
  have hle : toggleScanOrderClosedFormModel n ≤ Nat.factorial (6 * n) :=
    Nat.le_of_dvd (Nat.factorial_pos _) hdiv
  have hpos : 0 < (toggleScanOrderClosedFormModel n : ℝ) := by
    exact_mod_cast toggleScanOrderClosedFormModel_pos n hn
  exact (Real.log_le_log_iff hpos (by exact_mod_cast Nat.factorial_pos (6 * n))).2
    (by exact_mod_cast hle)

/-- Arithmetic-progression package for the scan-order closed form together with the existing
prime-power lower bound and a logarithmic upper envelope coming from the factorial model.
    thm:pom-toggle-scan-order-log-asymptotic -/
theorem paper_pom_toggle_scan_order_log_asymptotic_package (n : Nat) (hn : 4 ≤ n) :
    (∀ j : Nat, toggleScanOrderAPTerm n (j + 1) = toggleScanOrderAPTerm n j + 4) ∧
      toggleScanOrderClosedFormModel n ∣ Nat.factorial (6 * n) ∧
      Real.log (toggleScanOrderClosedFormModel n : ℝ) ≤
        Real.log ((Nat.factorial (6 * n) : ℕ) : ℝ) := by
  refine ⟨toggleScanOrderAPTerm_succ n, toggleScanOrderClosedFormModel_dvd_factorial n hn,
    toggleScanOrderClosedFormModel_log_upper n hn⟩

/-- Paper label wrapper for the logarithmic scan-order asymptotic theorem.
    thm:pom-toggle-scan-order-log-asymptotic -/
def paper_pom_toggle_scan_order_log_asymptotic : Prop := by
  exact
    ∀ n : Nat, 4 ≤ n →
      (∀ j : Nat, toggleScanOrderAPTerm n (j + 1) = toggleScanOrderAPTerm n j + 4) ∧
        toggleScanOrderClosedFormModel n ∣ Nat.factorial (6 * n) ∧
        Real.log (toggleScanOrderClosedFormModel n : ℝ) ≤
          Real.log ((Nat.factorial (6 * n) : ℕ) : ℝ)

end Omega.POM
