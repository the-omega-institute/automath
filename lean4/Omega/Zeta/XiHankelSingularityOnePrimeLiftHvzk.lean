import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

structure xi_hankel_singularity_one_prime_lift_hvzk_data where
  primeSet : Finset ℕ
  primeSet_nonempty : primeSet.Nonempty
  prime_mem : ∀ p ∈ primeSet, Nat.Prime p
  determinant : ℤ
  lowerPrimeCutoff : ℕ
  lowerPrimeCutoff_pos : 0 < lowerPrimeCutoff
  lowerBound : ∀ p ∈ primeSet, lowerPrimeCutoff ≤ p
  innerAcceptance : ℕ → ℚ
  innerAcceptance_le_one : ∀ p ∈ primeSet, innerAcceptance p ≤ 1
  honestCompleteness :
    ∀ p ∈ primeSet, determinant = 0 → 1 - (1 : ℚ) / p ≤ innerAcceptance p
  soundness :
    ∀ p ∈ primeSet, ¬ ((p : ℤ) ∣ determinant) → innerAcceptance p ≤ (1 : ℚ) / p
  innerRealTranscript : ℕ → ℕ → ℚ
  innerSimTranscript : ℕ → ℕ → ℚ
  simulator_exact :
    ∀ p ∈ primeSet, innerRealTranscript p = innerSimTranscript p

namespace xi_hankel_singularity_one_prime_lift_hvzk_data

def xi_hankel_singularity_one_prime_lift_hvzk_badPrimes
    (D : xi_hankel_singularity_one_prime_lift_hvzk_data) : Finset ℕ :=
  D.primeSet.filter fun p => ((p : ℤ) ∣ D.determinant)

def xi_hankel_singularity_one_prime_lift_hvzk_badPrimeProbability
    (D : xi_hankel_singularity_one_prime_lift_hvzk_data) : ℚ :=
  (D.xi_hankel_singularity_one_prime_lift_hvzk_badPrimes.card : ℚ) / D.primeSet.card

def xi_hankel_singularity_one_prime_lift_hvzk_averageInversePrime
    (D : xi_hankel_singularity_one_prime_lift_hvzk_data) : ℚ :=
  Finset.sum D.primeSet (fun p => (1 : ℚ) / p) / D.primeSet.card

def xi_hankel_singularity_one_prime_lift_hvzk_falseAcceptProbability
    (D : xi_hankel_singularity_one_prime_lift_hvzk_data) : ℚ :=
  Finset.sum D.primeSet (fun p => D.innerAcceptance p) / D.primeSet.card

def xi_hankel_singularity_one_prime_lift_hvzk_outerRealTranscript
    (D : xi_hankel_singularity_one_prime_lift_hvzk_data) (t : ℕ) : ℚ :=
  Finset.sum D.primeSet (fun p => D.innerRealTranscript p t) / D.primeSet.card

def xi_hankel_singularity_one_prime_lift_hvzk_outerSimTranscript
    (D : xi_hankel_singularity_one_prime_lift_hvzk_data) (t : ℕ) : ℚ :=
  Finset.sum D.primeSet (fun p => D.innerSimTranscript p t) / D.primeSet.card

def xi_hankel_singularity_one_prime_lift_hvzk_spec
    (D : xi_hankel_singularity_one_prime_lift_hvzk_data) : Prop :=
  (D.determinant = 0 →
    ∀ p ∈ D.primeSet, 1 - (1 : ℚ) / p ≤ D.innerAcceptance p) ∧
  (D.determinant ≠ 0 →
    D.xi_hankel_singularity_one_prime_lift_hvzk_falseAcceptProbability ≤
        D.xi_hankel_singularity_one_prime_lift_hvzk_badPrimeProbability +
          D.xi_hankel_singularity_one_prime_lift_hvzk_averageInversePrime ∧
      D.xi_hankel_singularity_one_prime_lift_hvzk_falseAcceptProbability ≤
        ((Int.natAbs D.determinant).primeFactors.card : ℚ) / D.primeSet.card +
          (1 : ℚ) / D.lowerPrimeCutoff) ∧
  (∀ t,
    D.xi_hankel_singularity_one_prime_lift_hvzk_outerRealTranscript t =
      D.xi_hankel_singularity_one_prime_lift_hvzk_outerSimTranscript t)

lemma xi_hankel_singularity_one_prime_lift_hvzk_card_pos
    (D : xi_hankel_singularity_one_prime_lift_hvzk_data) : 0 < D.primeSet.card := by
  rcases D.primeSet_nonempty with ⟨p, hp⟩
  exact Finset.card_pos.mpr ⟨p, hp⟩

lemma xi_hankel_singularity_one_prime_lift_hvzk_badPrime_subset_primeFactors
    (D : xi_hankel_singularity_one_prime_lift_hvzk_data) (hdet : D.determinant ≠ 0) :
    D.xi_hankel_singularity_one_prime_lift_hvzk_badPrimes ⊆
      (Int.natAbs D.determinant).primeFactors := by
  intro p hp
  have hp_mem : p ∈ D.primeSet := (Finset.mem_filter.mp hp).1
  have hp_dvd : ((p : ℤ) ∣ D.determinant) := (Finset.mem_filter.mp hp).2
  have hp_prime : Nat.Prime p := D.prime_mem p hp_mem
  have hp_natabs : p ∣ Int.natAbs D.determinant := by
    simpa using Int.natAbs_dvd_natAbs.mpr hp_dvd
  exact Nat.mem_primeFactors.mpr ⟨hp_prime, hp_natabs, Int.natAbs_ne_zero.mpr hdet⟩

lemma xi_hankel_singularity_one_prime_lift_hvzk_badPrimeProbability_le
    (D : xi_hankel_singularity_one_prime_lift_hvzk_data) (hdet : D.determinant ≠ 0) :
    D.xi_hankel_singularity_one_prime_lift_hvzk_badPrimeProbability ≤
      ((Int.natAbs D.determinant).primeFactors.card : ℚ) / D.primeSet.card := by
  have hsubset :=
    D.xi_hankel_singularity_one_prime_lift_hvzk_badPrime_subset_primeFactors hdet
  have hcard :
      D.xi_hankel_singularity_one_prime_lift_hvzk_badPrimes.card ≤
        (Int.natAbs D.determinant).primeFactors.card :=
    Finset.card_le_card hsubset
  have hcardq :
      (D.xi_hankel_singularity_one_prime_lift_hvzk_badPrimes.card : ℚ) ≤
        (Int.natAbs D.determinant).primeFactors.card := by
    exact_mod_cast hcard
  have hposq : (0 : ℚ) < D.primeSet.card := by
    exact_mod_cast D.xi_hankel_singularity_one_prime_lift_hvzk_card_pos
  exact div_le_div_of_nonneg_right hcardq hposq.le

lemma xi_hankel_singularity_one_prime_lift_hvzk_averageInversePrime_le
    (D : xi_hankel_singularity_one_prime_lift_hvzk_data) :
    D.xi_hankel_singularity_one_prime_lift_hvzk_averageInversePrime ≤
      (1 : ℚ) / D.lowerPrimeCutoff := by
  have hsum :
      Finset.sum D.primeSet (fun p => (1 : ℚ) / p) ≤
        Finset.sum D.primeSet (fun _ => (1 : ℚ) / D.lowerPrimeCutoff) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hcutoffq : (0 : ℚ) < D.lowerPrimeCutoff := by
      exact_mod_cast D.lowerPrimeCutoff_pos
    have hboundq : (D.lowerPrimeCutoff : ℚ) ≤ p := by
      exact_mod_cast D.lowerBound p hp
    exact one_div_le_one_div_of_le hcutoffq hboundq
  have hposq : (0 : ℚ) < D.primeSet.card := by
    exact_mod_cast D.xi_hankel_singularity_one_prime_lift_hvzk_card_pos
  calc
    D.xi_hankel_singularity_one_prime_lift_hvzk_averageInversePrime
        = Finset.sum D.primeSet (fun p => (1 : ℚ) / p) / D.primeSet.card := rfl
    _ ≤ Finset.sum D.primeSet (fun _ => (1 : ℚ) / D.lowerPrimeCutoff) / D.primeSet.card :=
      div_le_div_of_nonneg_right hsum hposq.le
    _ = (1 : ℚ) / D.lowerPrimeCutoff := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp [show (D.primeSet.card : ℚ) ≠ 0 by exact_mod_cast
        D.xi_hankel_singularity_one_prime_lift_hvzk_card_pos.ne']

lemma xi_hankel_singularity_one_prime_lift_hvzk_falseAccept_le_general
    (D : xi_hankel_singularity_one_prime_lift_hvzk_data) :
    D.xi_hankel_singularity_one_prime_lift_hvzk_falseAcceptProbability ≤
      D.xi_hankel_singularity_one_prime_lift_hvzk_badPrimeProbability +
        D.xi_hankel_singularity_one_prime_lift_hvzk_averageInversePrime := by
  have hpointwise :
      ∀ p ∈ D.primeSet,
        D.innerAcceptance p ≤
          (if ((p : ℤ) ∣ D.determinant) then (1 : ℚ) else 0) + (1 : ℚ) / p := by
    intro p hp
    by_cases hbad : ((p : ℤ) ∣ D.determinant)
    · have hone : D.innerAcceptance p ≤ 1 := D.innerAcceptance_le_one p hp
      have hnonneg : (0 : ℚ) ≤ (1 : ℚ) / p := by
        have hpq : (0 : ℚ) < p := by
          exact_mod_cast (D.prime_mem p hp).pos
        positivity
      have hbound : D.innerAcceptance p ≤ 1 + (1 : ℚ) / p := by
        linarith
      simpa [hbad] using hbound
    · have hsnd : D.innerAcceptance p ≤ (1 : ℚ) / p := D.soundness p hp hbad
      simpa [hbad] using hsnd
  have hsum :
      Finset.sum D.primeSet (fun p => D.innerAcceptance p) ≤
        Finset.sum D.primeSet
          (fun p => (if ((p : ℤ) ∣ D.determinant) then (1 : ℚ) else 0) + (1 : ℚ) / p) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    exact hpointwise p hp
  have hposq : (0 : ℚ) < D.primeSet.card := by
    exact_mod_cast D.xi_hankel_singularity_one_prime_lift_hvzk_card_pos
  calc
    D.xi_hankel_singularity_one_prime_lift_hvzk_falseAcceptProbability
        = Finset.sum D.primeSet (fun p => D.innerAcceptance p) / D.primeSet.card := rfl
    _ ≤
        Finset.sum D.primeSet
            (fun p => (if ((p : ℤ) ∣ D.determinant) then (1 : ℚ) else 0) + (1 : ℚ) / p) /
          D.primeSet.card := div_le_div_of_nonneg_right hsum hposq.le
    _ =
        D.xi_hankel_singularity_one_prime_lift_hvzk_badPrimeProbability +
          D.xi_hankel_singularity_one_prime_lift_hvzk_averageInversePrime := by
      rw [Finset.sum_add_distrib, add_div]
      simp [xi_hankel_singularity_one_prime_lift_hvzk_badPrimeProbability,
        xi_hankel_singularity_one_prime_lift_hvzk_averageInversePrime,
        xi_hankel_singularity_one_prime_lift_hvzk_badPrimes]

lemma xi_hankel_singularity_one_prime_lift_hvzk_falseAccept_le_explicit
    (D : xi_hankel_singularity_one_prime_lift_hvzk_data) (hdet : D.determinant ≠ 0) :
    D.xi_hankel_singularity_one_prime_lift_hvzk_falseAcceptProbability ≤
      ((Int.natAbs D.determinant).primeFactors.card : ℚ) / D.primeSet.card +
        (1 : ℚ) / D.lowerPrimeCutoff := by
  calc
    D.xi_hankel_singularity_one_prime_lift_hvzk_falseAcceptProbability
        ≤ D.xi_hankel_singularity_one_prime_lift_hvzk_badPrimeProbability +
            D.xi_hankel_singularity_one_prime_lift_hvzk_averageInversePrime :=
      D.xi_hankel_singularity_one_prime_lift_hvzk_falseAccept_le_general
    _ ≤ ((Int.natAbs D.determinant).primeFactors.card : ℚ) / D.primeSet.card +
          (1 : ℚ) / D.lowerPrimeCutoff := by
      gcongr
      · exact D.xi_hankel_singularity_one_prime_lift_hvzk_badPrimeProbability_le hdet
      · exact D.xi_hankel_singularity_one_prime_lift_hvzk_averageInversePrime_le

end xi_hankel_singularity_one_prime_lift_hvzk_data

open xi_hankel_singularity_one_prime_lift_hvzk_data

theorem paper_xi_hankel_singularity_one_prime_lift_hvzk
    (D : xi_hankel_singularity_one_prime_lift_hvzk_data) :
    xi_hankel_singularity_one_prime_lift_hvzk_spec D := by
  refine ⟨?_, ?_, ?_⟩
  · intro hdet p hp
    exact D.honestCompleteness p hp hdet
  · intro hdet
    exact ⟨D.xi_hankel_singularity_one_prime_lift_hvzk_falseAccept_le_general,
      D.xi_hankel_singularity_one_prime_lift_hvzk_falseAccept_le_explicit hdet⟩
  · intro t
    unfold xi_hankel_singularity_one_prime_lift_hvzk_outerRealTranscript
      xi_hankel_singularity_one_prime_lift_hvzk_outerSimTranscript
    simp [Finset.sum_congr rfl fun p hp => by
      simpa using congrFun (D.simulator_exact p hp) t]

end Omega.Zeta
