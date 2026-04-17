import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

namespace Omega.Zeta

/-- The number of sampled indices whose sampled value is a bad prime divisor of `Δ`. -/
def sampledBadPrimeCount {M : ℕ} (Δ : ℕ) (sample : Fin M → ℕ) : ℕ :=
  (Finset.univ.filter fun i => sample i ∈ Δ.primeFactors).card

/-- The sampling failure ratio is bounded by the bad-prime ratio in the ambient sample. -/
def failureProbabilityLeBadPrimeRatio {M : ℕ} (Δ : ℕ) (sample : Fin M → ℕ) : Prop :=
  (sampledBadPrimeCount Δ sample : ℚ) / (M : ℚ) ≤
    (Δ.primeFactors.card : ℚ) / (M : ℚ)

/-- The bad-prime ratio is bounded by the base-2 bitlength proxy coming from `2^ω(Δ) ≤ Δ`. -/
def badPrimeRatioLeBitlengthRatio (Δ M : ℕ) : Prop :=
  (Δ.primeFactors.card : ℚ) / (M : ℚ) ≤ (Nat.log2 Δ : ℚ) / (M : ℚ)

private theorem two_pow_card_le_prod_of_two_le :
    ∀ {s : Finset ℕ}, (∀ p ∈ s, 2 ≤ p) → 2 ^ s.card ≤ ∏ p ∈ s, p := by
  intro s hs
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hs' : ∀ p ∈ s, 2 ≤ p := fun p hp => hs p (by simp [hp])
      have ha2 : 2 ≤ a := hs a (by simp [ha])
      calc
        2 ^ (insert a s).card = 2 ^ s.card * 2 := by simp [ha, pow_succ, Nat.mul_comm]
        _ ≤ 2 ^ s.card * a := Nat.mul_le_mul_left _ ha2
        _ ≤ a * ∏ p ∈ s, p := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using Nat.mul_le_mul_left a (ih hs')
        _ = ∏ p ∈ insert a s, p := by simp [ha]

private theorem primeFactors_card_le_log2 (Δ : ℕ) (hΔ : Δ ≠ 0) :
    Δ.primeFactors.card ≤ Nat.log2 Δ := by
  have hprodLower : 2 ^ Δ.primeFactors.card ≤ ∏ p ∈ Δ.primeFactors, p := by
    apply two_pow_card_le_prod_of_two_le
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).two_le
  have hprodDvd : ∏ p ∈ Δ.primeFactors, p ∣ Δ := Nat.prod_primeFactors_dvd Δ
  have hprodLe : ∏ p ∈ Δ.primeFactors, p ≤ Δ := by
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hΔ) hprodDvd
  have hpowLe : 2 ^ Δ.primeFactors.card ≤ Δ := hprodLower.trans hprodLe
  simpa [Nat.log2_eq_log_two] using Nat.le_log_of_pow_le Nat.one_lt_two hpowLe

/-- Paper-facing bad-prime sampling bound:
the sampled failure ratio is bounded by the ratio of bad primes, which is in turn bounded by the
base-2 bitlength proxy `log2 Δ`.
cor:xi-hankel-badprime-selection-probability -/
theorem paper_xi_hankel_badprime_selection_probability
    {M : ℕ} (hM : 0 < M) (Δ : ℕ) (hΔ : Δ ≠ 0)
    (sample : Fin M → ℕ) (hinj : Function.Injective sample) :
    failureProbabilityLeBadPrimeRatio Δ sample ∧ badPrimeRatioLeBitlengthRatio Δ M := by
  constructor
  · unfold failureProbabilityLeBadPrimeRatio sampledBadPrimeCount
    let s : Finset (Fin M) := Finset.univ.filter fun i => sample i ∈ Δ.primeFactors
    change ((s.card : ℚ) / (M : ℚ) ≤ (Δ.primeFactors.card : ℚ) / (M : ℚ))
    have hs : s.image sample ⊆ Δ.primeFactors := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp hi).2
    have hcard : s.card ≤ Δ.primeFactors.card := by
      calc
        s.card = (s.image sample).card := (Finset.card_image_of_injective s hinj).symm
        _ ≤ Δ.primeFactors.card := Finset.card_le_card hs
    have hMq : (0 : ℚ) < (M : ℚ) := by exact_mod_cast hM
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hMq.le
  · have hω : Δ.primeFactors.card ≤ Nat.log2 Δ := primeFactors_card_le_log2 Δ hΔ
    have hMq : (0 : ℚ) < (M : ℚ) := by exact_mod_cast hM
    unfold badPrimeRatioLeBitlengthRatio
    exact div_le_div_of_nonneg_right (by exact_mod_cast hω) hMq.le

end Omega.Zeta
