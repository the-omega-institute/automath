import Mathlib
import Omega.Folding.TranslationKernelFourierSgM

namespace Omega.Folding

/-- The proper divisors of `m + 2`, which index the rigid cosets appearing in the sparse zero-set
bound. -/
def foldZeroProperDivisors (m : ℕ) : Finset ℕ :=
  (m + 2).divisors.erase (m + 2)

/-- The finite union of rigid frequency cosets modeled on the paper's zero set. -/
def foldZeroFrequencyUnion (m : ℕ) : Finset ℕ :=
  let M := Nat.fib (m + 2)
  (foldZeroProperDivisors m).biUnion fun d =>
    translationKernelCharacterFrequencies M (Nat.fib d)

lemma foldZeroProperDivisor_le_half (m d : ℕ) (hd : d ∈ foldZeroProperDivisors m) :
    d ≤ (m + 2) / 2 := by
  have hd_dvd : d ∣ m + 2 := Nat.dvd_of_mem_divisors (Finset.mem_of_mem_erase hd)
  have hd_ne : d ≠ m + 2 := Finset.ne_of_mem_erase hd
  have hmk_pos : 0 < m + 2 := by omega
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd hmk_pos
  obtain ⟨k, hk⟩ := hd_dvd
  have hk_pos : 0 < k := by
    by_contra hk0
    have hk_zero : k = 0 := Nat.eq_zero_of_not_pos hk0
    rw [hk_zero, Nat.mul_zero] at hk
    omega
  have hk_ne_one : k ≠ 1 := by
    intro hk1
    apply hd_ne
    simp [hk, hk1]
  have hk_ge_two : 2 ≤ k := by omega
  have hmul : d * 2 ≤ m + 2 := by
    calc
      d * 2 ≤ d * k := Nat.mul_le_mul_left d hk_ge_two
      _ = m + 2 := by simpa [Nat.mul_comm] using hk.symm
  omega

lemma translationKernelCharacterFrequencies_card_le_fib_half (m d : ℕ)
    (hd : d ∈ foldZeroProperDivisors m) :
    (translationKernelCharacterFrequencies (Nat.fib (m + 2)) (Nat.fib d)).card ≤
      Nat.fib ((m + 2) / 2) := by
  let M := Nat.fib (m + 2)
  let w := Nat.fib d
  have hMpos : 0 < M := by
    dsimp [M]
    exact Nat.fib_pos.mpr (by omega)
  have hd_pos : 0 < d := by
    have hd_dvd : d ∣ m + 2 := Nat.dvd_of_mem_divisors (Finset.mem_of_mem_erase hd)
    exact Nat.pos_of_dvd_of_pos hd_dvd (by omega)
  have hw_pos : 0 < w := by
    dsimp [w]
    exact Nat.fib_pos.mpr hd_pos
  have hd_half : d ≤ (m + 2) / 2 := foldZeroProperDivisor_le_half m d hd
  by_cases hEven : Even (sgMStep M w)
  · rw [translationKernelCharacterFrequencies, if_pos hEven]
    calc
      (sgMFrequencySet M w).card = Nat.gcd M w := sgMFrequencySet_card M w hMpos
      _ ≤ w := Nat.le_of_dvd hw_pos (Nat.gcd_dvd_right M w)
      _ = Nat.fib d := rfl
      _ ≤ Nat.fib ((m + 2) / 2) := Nat.fib_mono hd_half
  · rw [translationKernelCharacterFrequencies, if_neg hEven]
    exact Nat.zero_le _

/-- The zero-frequency union is bounded by the divisor count times the largest possible rigid coset
size, giving the Lean-side sparse-density estimate for `thm:fold-zero-density-sparse`. -/
theorem paper_fold_zero_density_sparse (m : ℕ) (hM : Even (Nat.fib (m + 2))) :
    let M := Nat.fib (m + 2)
    let Z := foldZeroFrequencyUnion m
    Z.card ≤ (m + 2).divisors.card * Nat.fib ((m + 2) / 2) ∧
      (Z.card : ℚ) / M ≤
        (((m + 2).divisors.card * Nat.fib ((m + 2) / 2) : ℕ) : ℚ) / M := by
  let M := Nat.fib (m + 2)
  let Z := foldZeroFrequencyUnion m
  let _ := hM
  have hMpos : 0 < M := by
    dsimp [M]
    exact Nat.fib_pos.mpr (by omega)
  have hcard_union :
      Z.card ≤ (foldZeroProperDivisors m).card * Nat.fib ((m + 2) / 2) := by
    dsimp [Z, foldZeroFrequencyUnion]
    exact Finset.card_biUnion_le_card_mul (foldZeroProperDivisors m)
      (fun d => translationKernelCharacterFrequencies (Nat.fib (m + 2)) (Nat.fib d))
      (Nat.fib ((m + 2) / 2))
      (by
        intro d hd
        exact translationKernelCharacterFrequencies_card_le_fib_half m d hd)
  have hproper :
      (foldZeroProperDivisors m).card ≤ (m + 2).divisors.card := by
    exact Finset.card_le_card (Finset.erase_subset (m + 2) (m + 2).divisors)
  have hcard :
      Z.card ≤ (m + 2).divisors.card * Nat.fib ((m + 2) / 2) := by
    calc
      Z.card ≤ (foldZeroProperDivisors m).card * Nat.fib ((m + 2) / 2) := hcard_union
      _ ≤ (m + 2).divisors.card * Nat.fib ((m + 2) / 2) :=
        Nat.mul_le_mul_right _ hproper
  have hratio :
      (Z.card : ℚ) / M ≤
        (((m + 2).divisors.card * Nat.fib ((m + 2) / 2) : ℕ) : ℚ) / M := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  exact ⟨hcard, hratio⟩

end Omega.Folding
