import Mathlib.Tactic

namespace Omega.StatisticalStability

/-- Empirical precision of a sieve: accepted primes divided by accepted integers. -/
noncomputable def primeSievePrecision (acceptedPrimes acceptedSet : ℕ → ℝ) (X : ℕ) : ℝ :=
  acceptedPrimes X / acceptedSet X

private theorem primeSievePrecision_bound
    (M phiM : ℝ) (acceptedPrimes acceptedSet : ℕ → ℝ)
    (hM : 0 < M) (hphi : 0 < phiM)
    (hPrime : ∀ X : ℕ, X ≥ 2 → acceptedPrimes X ≤ (1 / phiM) * (X : ℝ) / Real.log (X : ℝ))
    (hSet : ∀ X : ℕ, X ≥ 2 → (1 / M) * (X : ℝ) ≤ acceptedSet X) :
    ∀ X : ℕ, X ≥ 2 → primeSievePrecision acceptedPrimes acceptedSet X ≤
      (M / phiM) / Real.log (X : ℝ) := by
  intro X hX
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hX)
  have hlog_pos : 0 < Real.log (X : ℝ) := by
    have hXgt1 : (1 : ℝ) < X := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < (2 : ℕ)) hX)
    exact Real.log_pos hXgt1
  have hden_lower_pos : 0 < (1 / M) * (X : ℝ) := by positivity
  have hden_pos : 0 < acceptedSet X := lt_of_lt_of_le hden_lower_pos (hSet X hX)
  have hnum_upper_nonneg : 0 ≤ (1 / phiM) * (X : ℝ) / Real.log (X : ℝ) := by positivity
  have hstep1 :
      primeSievePrecision acceptedPrimes acceptedSet X ≤
        ((1 / phiM) * (X : ℝ) / Real.log (X : ℝ)) / acceptedSet X := by
    unfold primeSievePrecision
    exact div_le_div_of_nonneg_right (hPrime X hX) (le_of_lt hden_pos)
  have hstep2 :
      ((1 / phiM) * (X : ℝ) / Real.log (X : ℝ)) / acceptedSet X ≤
        ((1 / phiM) * (X : ℝ) / Real.log (X : ℝ)) / ((1 / M) * (X : ℝ)) := by
    have hInv :
        1 / acceptedSet X ≤ 1 / ((1 / M) * (X : ℝ)) := by
      exact one_div_le_one_div_of_le hden_lower_pos (hSet X hX)
    simpa [div_eq_mul_inv, one_div] using mul_le_mul_of_nonneg_left hInv hnum_upper_nonneg
  have hratio :
      ((1 / phiM) * (X : ℝ) / Real.log (X : ℝ)) / ((1 / M) * (X : ℝ)) =
        (M / phiM) / Real.log (X : ℝ) := by
    field_simp [hM.ne', hphi.ne', hXpos.ne', hlog_pos.ne']
  calc
    primeSievePrecision acceptedPrimes acceptedSet X ≤
        ((1 / phiM) * (X : ℝ) / Real.log (X : ℝ)) / acceptedSet X := hstep1
    _ ≤ ((1 / phiM) * (X : ℝ) / Real.log (X : ℝ)) / ((1 / M) * (X : ℝ)) := hstep2
    _ = (M / phiM) / Real.log (X : ℝ) := hratio

/-- Paper-facing fixed-resolution prime-sieve precision bound. An abstract upper bound on accepted
primes in coprime residue classes and an abstract lower-density estimate for the accepted set
combine to give the `M / φ(M)` prefactor; any eventual decay of the `1 / log X` term forces the
precision to tend to zero.
    thm:fixed-resolution-prime-sieve-precision-to-zero -/
theorem paper_fixed_resolution_prime_sieve_precision_to_zero
    (M phiM : ℝ) (acceptedPrimes acceptedSet : ℕ → ℝ)
    (hM : 0 < M) (hphi : 0 < phiM)
    (hPrime : ∀ X : ℕ, X ≥ 2 → acceptedPrimes X ≤ (1 / phiM) * (X : ℝ) / Real.log (X : ℝ))
    (hSet : ∀ X : ℕ, X ≥ 2 → (1 / M) * (X : ℝ) ≤ acceptedSet X)
    (hDecay : ∀ ε > 0, ∃ X0 : ℕ, 2 ≤ X0 ∧
      ∀ X : ℕ, X ≥ X0 → (M / phiM) / Real.log (X : ℝ) ≤ ε) :
    (∀ X : ℕ, X ≥ 2 → primeSievePrecision acceptedPrimes acceptedSet X ≤
      (M / phiM) / Real.log (X : ℝ)) ∧
      ∀ ε > 0, ∃ X0 : ℕ, 2 ≤ X0 ∧
        ∀ X : ℕ, X ≥ X0 → primeSievePrecision acceptedPrimes acceptedSet X ≤ ε := by
  have hBound :
      ∀ X : ℕ, X ≥ 2 → primeSievePrecision acceptedPrimes acceptedSet X ≤
        (M / phiM) / Real.log (X : ℝ) :=
    primeSievePrecision_bound M phiM acceptedPrimes acceptedSet hM hphi hPrime hSet
  constructor
  · exact hBound
  · intro ε hε
    rcases hDecay ε hε with ⟨X0, hX0, hX0bound⟩
    refine ⟨X0, hX0, ?_⟩
    intro X hX
    exact (hBound X (le_trans hX0 hX)).trans (hX0bound X hX)

end Omega.StatisticalStability
