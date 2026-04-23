import Mathlib.Tactic
import Omega.Core.Fib
import Omega.Folding.TranslationKernelFourierSgM

namespace Omega.Folding

/-- The proper divisors of `m + 2`, used here as the admissible divisor witnesses. -/
def fold_zero_divisor_lb_properDivisors (m : ℕ) : Finset ℕ :=
  (m + 2).divisors.erase (m + 2)

/-- The concrete union of rigid cosets contributed by those divisor witnesses. -/
def fold_zero_divisor_lb_frequencyUnion (m : ℕ) : Finset ℕ :=
  let M := Nat.fib (m + 2)
  (fold_zero_divisor_lb_properDivisors m).biUnion fun d =>
    translationKernelCharacterFrequencies M (Nat.fib d)

private lemma fold_zero_divisor_lb_step_even
    (M w : ℕ) (hMpos : 0 < M) (hM : Even M) (hgcd : Nat.gcd M w = w) (hdiv : w ∣ M / 2) :
    Even (sgMStep M w) := by
  have hwpos : 0 < w := by
    simpa [hgcd] using Nat.gcd_pos_of_pos_left w hMpos
  rcases hM with ⟨n, rfl⟩
  rcases hdiv with ⟨q, hq⟩
  have hq' : n = w * q := by
    omega
  refine ⟨q, ?_⟩
  unfold sgMStep
  rw [hgcd]
  have hsum : n + n = w * (q + q) := by
    rw [hq']
    ring
  rw [hsum, Nat.mul_div_right _ hwpos]

/-- Paper label: `cor:fold-zero-divisor-lb`.
In the even-Fibonacci regime, every proper divisor witness `d` with `F_d ∣ F_{m+2} / 2`
contributes the concrete rigid coset `S_{F_d}(F_{m+2})` to the modeled zero-frequency union, so
the union has cardinality at least `F_d`. -/
theorem paper_fold_zero_divisor_lb (m : ℕ) (hM : Even (Nat.fib (m + 2))) :
    ∀ d ∈ fold_zero_divisor_lb_properDivisors m,
      Nat.fib d ∣ Nat.fib (m + 2) / 2 →
        (translationKernelCharacterFrequencies (Nat.fib (m + 2)) (Nat.fib d)).card = Nat.fib d ∧
          Nat.fib d ≤ (fold_zero_divisor_lb_frequencyUnion m).card := by
  intro d hd hdiv
  let M := Nat.fib (m + 2)
  let w := Nat.fib d
  have hMpos : 0 < M := by
    dsimp [M]
    exact Nat.fib_pos.mpr (by omega)
  have hd_dvd : d ∣ m + 2 := Nat.dvd_of_mem_divisors (Finset.mem_of_mem_erase hd)
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd (by omega)
  have hw_dvd : w ∣ M := by
    dsimp [M, w]
    exact Nat.fib_dvd d (m + 2) hd_dvd
  have hw_pos : 0 < w := by
    dsimp [w]
    exact Nat.fib_pos.mpr hd_pos
  have hgcd : Nat.gcd M w = w := Nat.gcd_eq_right hw_dvd
  have hstep_even : Even (sgMStep M w) := by
    exact fold_zero_divisor_lb_step_even M w hMpos (by simpa [M] using hM) hgcd
      (by simpa [M, w] using hdiv)
  have hcard :
      (translationKernelCharacterFrequencies M w).card = w := by
    have hFourier := paper_fold_translation_kernel_fourier_sgM M w hMpos
    simpa [hgcd] using hFourier.2.2.2.2 hstep_even
  have hsubset :
      translationKernelCharacterFrequencies M w ⊆ fold_zero_divisor_lb_frequencyUnion m := by
    intro t ht
    dsimp [fold_zero_divisor_lb_frequencyUnion, fold_zero_divisor_lb_properDivisors, M, w]
    exact Finset.mem_biUnion.mpr ⟨d, hd, ht⟩
  have hlower : w ≤ (fold_zero_divisor_lb_frequencyUnion m).card := by
    calc
      w = (translationKernelCharacterFrequencies M w).card := hcard.symm
      _ ≤ (fold_zero_divisor_lb_frequencyUnion m).card := Finset.card_le_card hsubset
  simpa [M, w] using ⟨hcard, hlower⟩

end Omega.Folding
