import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- The leading second-collision contribution to the Bayes-optimal InfoNCE objective. -/
def bayesInfonceSecondCollisionMainTerm (K : ℕ) (M2 : ℝ) : ℝ :=
  ((K - 1 : ℝ) * Real.log 2) * M2

/-- A chapter-local deterministic coefficient controlling the `J ≥ 2` remainder. -/
def bayesInfonceSecondCollisionRemainderCoeff (K : ℕ) : ℝ :=
  (K : ℝ) * Real.log (K + 1)

/-- The exponential scale extracted from the Perron-Frobenius asymptotic `S₂(m) = r₂^m`. -/
def bayesInfonceExponentialScale (r2 : ℝ) (m : ℕ) : ℝ :=
  (r2 / 4) ^ m

/-- If the Bayes-optimal InfoNCE value decomposes into the second-collision main term plus a third
moment remainder, and `M₃(m) ≤ w_max(m) M₂(m)`, then the second-collision term dominates. Under
the exact Perron-Frobenius asymptotic `S₂(m) = r₂^m`, the collision moment itself has scale
`(r₂ / 4)^m`.
    thm:pom-bayes-infonce-second-collision-dominance -/
theorem paper_pom_bayes_infonce_second_collision_dominance
    (K : ℕ) (Lstar M2 M3 wmax S2 : ℕ → ℝ) (r2 : ℝ)
    (hrepr : ∀ m,
      Lstar m =
        bayesInfonceSecondCollisionMainTerm K (M2 m) +
          bayesInfonceSecondCollisionRemainderCoeff K * M3 m)
    (hM3 : ∀ m, M3 m ≤ wmax m * M2 m)
    (hS2 : ∀ m, S2 m = (4 : ℝ) ^ m * M2 m)
    (hpf : ∀ m, S2 m = r2 ^ m) :
    (∀ m, Lstar m ≤ bayesInfonceSecondCollisionMainTerm K (M2 m) +
      bayesInfonceSecondCollisionRemainderCoeff K * wmax m * M2 m) ∧
    (∀ m, Lstar m ≤
      (((K - 1 : ℝ) * Real.log 2) +
        bayesInfonceSecondCollisionRemainderCoeff K * wmax m) * M2 m) ∧
    (∀ m, M2 m = bayesInfonceExponentialScale r2 m) := by
  have hcoeff_nonneg : 0 ≤ bayesInfonceSecondCollisionRemainderCoeff K := by
    unfold bayesInfonceSecondCollisionRemainderCoeff
    have hlog_nonneg : 0 ≤ Real.log (K + 1) := by
      have hone : (1 : ℝ) ≤ (K + 1 : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le K)
      exact Real.log_nonneg hone
    exact mul_nonneg (by positivity) hlog_nonneg
  refine ⟨?_, ?_, ?_⟩
  · intro m
    have hmul :
        bayesInfonceSecondCollisionRemainderCoeff K * M3 m ≤
          bayesInfonceSecondCollisionRemainderCoeff K * (wmax m * M2 m) := by
      exact mul_le_mul_of_nonneg_left (hM3 m) hcoeff_nonneg
    calc
      Lstar m =
          bayesInfonceSecondCollisionMainTerm K (M2 m) +
            bayesInfonceSecondCollisionRemainderCoeff K * M3 m := hrepr m
      _ ≤ bayesInfonceSecondCollisionMainTerm K (M2 m) +
            bayesInfonceSecondCollisionRemainderCoeff K * (wmax m * M2 m) := by
          linarith
      _ = bayesInfonceSecondCollisionMainTerm K (M2 m) +
            bayesInfonceSecondCollisionRemainderCoeff K * wmax m * M2 m := by
          ring
  · intro m
    have hmul :
        bayesInfonceSecondCollisionRemainderCoeff K * M3 m ≤
          bayesInfonceSecondCollisionRemainderCoeff K * (wmax m * M2 m) := by
      exact mul_le_mul_of_nonneg_left (hM3 m) hcoeff_nonneg
    have hdom :
        Lstar m ≤ bayesInfonceSecondCollisionMainTerm K (M2 m) +
          bayesInfonceSecondCollisionRemainderCoeff K * (wmax m * M2 m) := by
      calc
        Lstar m =
            bayesInfonceSecondCollisionMainTerm K (M2 m) +
              bayesInfonceSecondCollisionRemainderCoeff K * M3 m := hrepr m
        _ ≤ bayesInfonceSecondCollisionMainTerm K (M2 m) +
              bayesInfonceSecondCollisionRemainderCoeff K * (wmax m * M2 m) := by
            linarith
    calc
      Lstar m ≤ bayesInfonceSecondCollisionMainTerm K (M2 m) +
          bayesInfonceSecondCollisionRemainderCoeff K * (wmax m * M2 m) := hdom
      _ = (((K - 1 : ℝ) * Real.log 2) +
            bayesInfonceSecondCollisionRemainderCoeff K * wmax m) * M2 m := by
          unfold bayesInfonceSecondCollisionMainTerm
          ring
  · intro m
    have hpow4_ne : (4 : ℝ) ^ m ≠ 0 := by positivity
    have hm2 :
        M2 m = r2 ^ m / (4 : ℝ) ^ m := by
      apply (eq_div_iff hpow4_ne).2
      rw [mul_comm]
      calc
        (4 : ℝ) ^ m * M2 m = S2 m := (hS2 m).symm
        _ = r2 ^ m := hpf m
    calc
      M2 m = r2 ^ m / (4 : ℝ) ^ m := hm2
      _ = (r2 / 4) ^ m := by
        calc
          r2 ^ m / (4 : ℝ) ^ m = r2 ^ m * ((4 : ℝ) ^ m)⁻¹ := by rw [div_eq_mul_inv]
          _ = r2 ^ m * ((4 : ℝ)⁻¹) ^ m := by rw [inv_pow]
          _ = (r2 * (4 : ℝ)⁻¹) ^ m := by rw [← mul_pow]
          _ = (r2 / 4) ^ m := by rw [div_eq_mul_inv]
      _ = bayesInfonceExponentialScale r2 m := rfl

end

end Omega.POM
