import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

namespace Omega.EA

open scoped BigOperators

/-- Gödel multiplicative scale of an exponent vector against a prime sequence.
    prop:prime-register-godel-log-busemann-time -/
noncomputable def godelScale (a : ℕ →₀ ℕ) (primes : ℕ → ℝ) : ℝ :=
  ∏ p ∈ a.support, (primes p) ^ (a p)

/-- Logarithmic Busemann time: the log of the Gödel scale.
    prop:prime-register-godel-log-busemann-time -/
noncomputable def godelLogTime (a : ℕ →₀ ℕ) (primes : ℕ → ℝ) : ℝ :=
  Real.log (godelScale a primes)

/-- Gödel scale of the zero exponent vector is 1.
    prop:prime-register-godel-log-busemann-time -/
theorem godelScale_zero (primes : ℕ → ℝ) : godelScale 0 primes = 1 := by
  unfold godelScale
  rw [Finsupp.support_zero, Finset.prod_empty]

/-- Log-time of the zero exponent vector is 0.
    prop:prime-register-godel-log-busemann-time -/
theorem godelLogTime_zero (primes : ℕ → ℝ) : godelLogTime 0 primes = 0 := by
  unfold godelLogTime
  rw [godelScale_zero, Real.log_one]

/-- Log-time expands as a weighted sum of log-primes.
    prop:prime-register-godel-log-busemann-time -/
theorem godelLogTime_eq_sum
    (a : ℕ →₀ ℕ) (primes : ℕ → ℝ)
    (hpos : ∀ p ∈ a.support, 0 < primes p) :
    godelLogTime a primes =
      ∑ p ∈ a.support, (a p : ℝ) * Real.log (primes p) := by
  unfold godelLogTime godelScale
  rw [Real.log_prod (fun p hp => pow_ne_zero _ (ne_of_gt (hpos p hp)))]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [Real.log_pow]

/-- Gödel scale is multiplicative under addition of exponents, provided all
    primes involved are positive.
    prop:prime-register-godel-log-busemann-time -/
theorem godelScale_add
    (a b : ℕ →₀ ℕ) (primes : ℕ → ℝ)
    (_hab_pos : ∀ p ∈ (a + b).support, 0 < primes p)
    (_ha_pos : ∀ p ∈ a.support, 0 < primes p)
    (_hb_pos : ∀ p ∈ b.support, 0 < primes p) :
    godelScale (a + b) primes = godelScale a primes * godelScale b primes := by
  classical
  unfold godelScale
  -- Extend the three products to the common support `a.support ∪ b.support`.
  have hExt_ab : (∏ p ∈ (a + b).support, primes p ^ (a + b) p) =
                 ∏ p ∈ a.support ∪ b.support, primes p ^ (a + b) p := by
    refine Finset.prod_subset Finsupp.support_add ?_
    intro p _ hp_notin
    have hzero : (a + b) p = 0 := by
      rwa [Finsupp.notMem_support_iff] at hp_notin
    rw [hzero, pow_zero]
  have hExt_a : (∏ p ∈ a.support, primes p ^ a p) =
                ∏ p ∈ a.support ∪ b.support, primes p ^ a p := by
    refine Finset.prod_subset Finset.subset_union_left ?_
    intro p _ hp_notin
    have hzero : a p = 0 := by
      rwa [Finsupp.notMem_support_iff] at hp_notin
    rw [hzero, pow_zero]
  have hExt_b : (∏ p ∈ b.support, primes p ^ b p) =
                ∏ p ∈ a.support ∪ b.support, primes p ^ b p := by
    refine Finset.prod_subset Finset.subset_union_right ?_
    intro p _ hp_notin
    have hzero : b p = 0 := by
      rwa [Finsupp.notMem_support_iff] at hp_notin
    rw [hzero, pow_zero]
  rw [hExt_ab, hExt_a, hExt_b, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro p _
  rw [Finsupp.add_apply, pow_add]

/-- Log-time is additive: `godelLogTime (a + b) = godelLogTime a + godelLogTime b`.
    prop:prime-register-godel-log-busemann-time -/
theorem godelLogTime_add
    (a b : ℕ →₀ ℕ) (primes : ℕ → ℝ)
    (hab_pos : ∀ p ∈ (a + b).support, 0 < primes p)
    (ha_pos : ∀ p ∈ a.support, 0 < primes p)
    (hb_pos : ∀ p ∈ b.support, 0 < primes p) :
    godelLogTime (a + b) primes = godelLogTime a primes + godelLogTime b primes := by
  unfold godelLogTime
  rw [godelScale_add a b primes hab_pos ha_pos hb_pos]
  have ha_scale_pos : 0 < godelScale a primes := by
    unfold godelScale
    exact Finset.prod_pos (fun p hp => pow_pos (ha_pos p hp) _)
  have hb_scale_pos : 0 < godelScale b primes := by
    unfold godelScale
    exact Finset.prod_pos (fun p hp => pow_pos (hb_pos p hp) _)
  exact Real.log_mul (ne_of_gt ha_scale_pos) (ne_of_gt hb_scale_pos)

/-- Paper package: Gödel logarithmic Busemann time is an additive homomorphism
    from exponent vectors to the real line.
    prop:prime-register-godel-log-busemann-time -/
theorem paper_prime_register_godel_log_busemann_time :
    (∀ primes : ℕ → ℝ, godelScale 0 primes = 1) ∧
    (∀ primes : ℕ → ℝ, godelLogTime 0 primes = 0) ∧
    (∀ (a : ℕ →₀ ℕ) (primes : ℕ → ℝ),
      (∀ p ∈ a.support, 0 < primes p) →
      godelLogTime a primes =
        ∑ p ∈ a.support, (a p : ℝ) * Real.log (primes p)) ∧
    (∀ (a b : ℕ →₀ ℕ) (primes : ℕ → ℝ),
      (∀ p ∈ (a + b).support, 0 < primes p) →
      (∀ p ∈ a.support, 0 < primes p) →
      (∀ p ∈ b.support, 0 < primes p) →
      godelLogTime (a + b) primes =
        godelLogTime a primes + godelLogTime b primes) :=
  ⟨godelScale_zero, godelLogTime_zero, godelLogTime_eq_sum, godelLogTime_add⟩

end Omega.EA
