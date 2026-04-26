import Mathlib.Tactic
import Omega.Folding.Entropy

open scoped goldenRatio

namespace Omega

private lemma pom_resolution_threshold_fib_lower_phi_pow_pair :
    ∀ n : ℕ, φ ^ n ≤ (Nat.fib (n + 2) : ℝ) ∧
      φ ^ (n + 1) ≤ (Nat.fib (n + 3) : ℝ)
  | 0 => by
      constructor
      · simp
      · norm_num [Nat.fib]
        exact le_of_lt Real.goldenRatio_lt_two
  | n + 1 => by
      rcases pom_resolution_threshold_fib_lower_phi_pow_pair n with ⟨hn, hn1⟩
      constructor
      · exact hn1
      · have hphi_rec : φ ^ (n + 2) = φ ^ n + φ ^ (n + 1) := by
          calc
            φ ^ (n + 2) = φ ^ n * φ ^ 2 := by simp [pow_add]
            _ = φ ^ n * (φ + 1) := by rw [Real.goldenRatio_sq]
            _ = φ ^ n + φ ^ (n + 1) := by ring
        have hfib_nat : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (Nat.fib_add_two (n := n + 2))
        have hfib : (Nat.fib (n + 4) : ℝ) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
          exact_mod_cast hfib_nat
        calc
          φ ^ (n + 2) = φ ^ n + φ ^ (n + 1) := hphi_rec
          _ ≤ (Nat.fib (n + 2) : ℝ) + Nat.fib (n + 3) := by gcongr
          _ = (Nat.fib (n + 4) : ℝ) := by simpa [add_comm] using hfib.symm

private lemma pom_resolution_threshold_fib_lower_phi_pow (n : ℕ) :
    φ ^ n ≤ (Nat.fib (n + 2) : ℝ) :=
  (pom_resolution_threshold_fib_lower_phi_pow_pair n).1

/-- Paper label: `cor:pom-resolution-threshold`. The fold index is bounded by the
golden-ratio exponential envelope with constant `1`. -/
theorem paper_pom_resolution_threshold :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, Omega.Entropy.foldIndex m ≤ C * (2 / φ) ^ m := by
  refine ⟨1, by norm_num, ?_⟩
  intro m
  have hphi_pos : 0 < (φ : ℝ) := Real.goldenRatio_pos
  have hphi_pow_pos : 0 < (φ : ℝ) ^ m := pow_pos hphi_pos m
  have hfib_pos : 0 < (Nat.fib (m + 2) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hfib_lower : (φ : ℝ) ^ m ≤ (Nat.fib (m + 2) : ℝ) :=
    pom_resolution_threshold_fib_lower_phi_pow m
  rw [Omega.Entropy.foldIndex, one_mul, div_pow]
  exact div_le_div_of_nonneg_left (by positivity) hphi_pow_pos hfib_lower

end Omega
