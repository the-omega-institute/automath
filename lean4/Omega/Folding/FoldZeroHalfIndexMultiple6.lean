import Mathlib
import Omega.Core.Fib
import Omega.Folding.FoldZeroDensitySparse
import Omega.Folding.ShiftDynamics

namespace Omega.Folding

/-- Paper label: `cor:fold-zero-half-index-multiple6`. When `m + 2` is a multiple of `6`, the
half-index Fibonacci divisor produces a visible rigid coset inside the modeled fold-zero set, so
the union has cardinality at least `F_{(m+2)/2}`. -/
theorem paper_fold_zero_half_index_multiple6 (m : ℕ) (hm : (m + 2) % 6 = 0) :
    Nat.fib ((m + 2) / 2) ∣ Nat.fib (m + 2) / 2 ∧
      Nat.fib ((m + 2) / 2) ≤ (foldZeroFrequencyUnion m).card := by
  let d := (m + 2) / 2
  let M := Nat.fib (m + 2)
  let w := Nat.fib d
  have hd_eq : m + 2 = 2 * d := by
    dsimp [d]
    omega
  have hd_pos : 0 < d := by
    dsimp [d]
    omega
  have hd_dvd : d ∣ m + 2 := by
    refine ⟨2, ?_⟩
    omega
  have hd_ne_top : d ≠ m + 2 := by
    omega
  have hd_mem : d ∈ foldZeroProperDivisors m := by
    dsimp [foldZeroProperDivisors]
    exact Finset.mem_erase.mpr
      ⟨hd_ne_top, Nat.mem_divisors.mpr ⟨hd_dvd, by omega⟩⟩
  have hd_three : 3 ∣ d := by
    dsimp [d]
    omega
  have hlucas_even : Even (Omega.lucasNum d) := by
    rcases (Omega.lucasNum_even_iff d).2 hd_three with ⟨r, hr⟩
    exact ⟨r, by simpa [two_mul] using hr⟩
  have hdouble : M = w * Omega.lucasNum d := by
    dsimp [M, w]
    calc
      Nat.fib (m + 2) = Nat.fib (2 * d) := by rw [hd_eq]
      _ = Nat.fib d * Omega.lucasNum d := Omega.fib_double_eq_mul_lucas d
  have hdiv_half : Nat.fib d ∣ Nat.fib (m + 2) / 2 := by
    rcases hlucas_even with ⟨k, hk⟩
    have hdouble_nat : Nat.fib (m + 2) = w * Omega.lucasNum d := by
      simpa [M] using hdouble
    refine ⟨k, ?_⟩
    calc
      Nat.fib (m + 2) / 2 = (w * Omega.lucasNum d) / 2 := by rw [hdouble_nat]
      _ = (w * (k + k)) / 2 := by rw [hk]
      _ = (2 * (w * k)) / 2 := by ring
      _ = w * k := by
        exact Nat.mul_div_right (w * k) (by decide)
      _ = Nat.fib d * k := by rfl
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Nat.fib_pos.mpr (by omega)
  have hw_pos : 0 < w := by
    dsimp [w]
    exact Nat.fib_pos.mpr hd_pos
  have hw_dvd : w ∣ M := by
    dsimp [M, w]
    exact Nat.fib_dvd d (m + 2) hd_dvd
  have hgcd : Nat.gcd M w = w := Nat.gcd_eq_right hw_dvd
  have hstep : sgMStep M w = Omega.lucasNum d := by
    unfold sgMStep
    rw [hgcd]
    have hdouble' : M = Omega.lucasNum d * w := by simpa [Nat.mul_comm] using hdouble
    rw [hdouble']
    simpa [Nat.mul_comm] using (Nat.mul_div_right (Omega.lucasNum d) hw_pos)
  have hstep_even : Even (sgMStep M w) := by
    rw [hstep]
    exact hlucas_even
  have hcard_w : (translationKernelCharacterFrequencies M w).card = w := by
    rw [translationKernelCharacterFrequencies, if_pos hstep_even, sgMFrequencySet_card M w hM_pos, hgcd]
  have hsubset : translationKernelCharacterFrequencies M w ⊆ foldZeroFrequencyUnion m := by
    intro t ht
    have ht' : t ∈ translationKernelCharacterFrequencies (Nat.fib (m + 2)) (Nat.fib d) := by
      simpa [M, w] using ht
    exact Finset.mem_biUnion.mpr ⟨d, hd_mem, ht'⟩
  have hcard_lower : Nat.fib d ≤ (foldZeroFrequencyUnion m).card := by
    calc
      Nat.fib d = (translationKernelCharacterFrequencies M w).card := by simpa [w] using hcard_w.symm
      _ ≤ (foldZeroFrequencyUnion m).card := Finset.card_le_card hsubset
  exact ⟨by simpa [d] using hdiv_half, by simpa [d] using hcard_lower⟩

end Omega.Folding
