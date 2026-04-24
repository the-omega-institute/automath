import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Tactic
import Omega.CircleDimension.ArithmeticSingularRingObservableClosureDichotomy

namespace Omega.Zeta

open scoped BigOperators

private lemma xi_prime_phase_torus_dense_uniquely_ergodic_prime_log_ratio_irrational {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    Irrational (Real.log (p : ℝ) / Real.log (q : ℝ)) := by
  rw [Irrational]
  intro hRat
  rcases hRat with ⟨r, hr⟩
  let k : ℕ := Int.toNat r.num
  have hp_gt : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hq_gt : 1 < (q : ℝ) := by exact_mod_cast hq.one_lt
  have hp_pos : 0 < (p : ℝ) := by positivity
  have hq_pos : 0 < (q : ℝ) := by positivity
  have hp_log_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp_gt
  have hq_log_pos : 0 < Real.log (q : ℝ) := Real.log_pos hq_gt
  have hq_log_ne : Real.log (q : ℝ) ≠ 0 := hq_log_pos.ne'
  have hratio_pos : 0 < Real.log (p : ℝ) / Real.log (q : ℝ) := by
    exact div_pos hp_log_pos hq_log_pos
  have hr_pos_real : (0 : ℝ) < r := by
    simpa [hr] using hratio_pos
  have hr_pos : 0 < r := by
    exact (Rat.cast_pos (K := ℝ) (q := r)).mp hr_pos_real
  have hnum_pos : 0 < r.num := Rat.num_pos.mpr hr_pos
  have hk_ne : k ≠ 0 := by
    intro hk0
    have hk0' : Int.toNat r.num = 0 := by simpa [k] using hk0
    have hk0_le : r.num ≤ 0 := Int.toNat_eq_zero.mp hk0'
    exact (not_le_of_gt hnum_pos) hk0_le
  have hk_cast_int : (k : ℤ) = r.num := by
    simpa [k] using Int.toNat_of_nonneg hnum_pos.le
  have hk_cast : (k : ℝ) = (r.num : ℝ) := by
    exact_mod_cast hk_cast_int
  have hden_ne : (r.den : ℝ) ≠ 0 := by positivity
  have hratio : Real.log (p : ℝ) / Real.log (q : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
    simpa [Rat.cast_def] using hr.symm
  have hcross : (r.den : ℝ) * Real.log (p : ℝ) = (r.num : ℝ) * Real.log (q : ℝ) := by
    field_simp [hq_log_ne, hden_ne] at hratio
    linarith
  have hpow_log : (r.den : ℝ) * Real.log (p : ℝ) = (k : ℝ) * Real.log (q : ℝ) := by
    rw [hk_cast]
    exact hcross
  have hpow_real : (p : ℝ) ^ r.den = (q : ℝ) ^ k := by
    calc
      (p : ℝ) ^ r.den = Real.exp ((r.den : ℝ) * Real.log (p : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hp_pos]
      _ = Real.exp ((k : ℝ) * Real.log (q : ℝ)) := by rw [hpow_log]
      _ = (q : ℝ) ^ k := by
        rw [Real.exp_nat_mul, Real.exp_log hq_pos]
  have hpow_nat : p ^ r.den = q ^ k := by
    exact_mod_cast hpow_real
  have hp_eq_q : p = q :=
    (Nat.Prime.pow_inj' hp hq (Nat.ne_zero_of_lt r.den_pos) hk_ne hpow_nat).1
  exact hpq hp_eq_q

private lemma xi_prime_phase_torus_dense_uniquely_ergodic_frequency_pos {L : ℕ} (hL : L ≠ 0)
    (p : L.primeFactors) :
    0 < 2 * (Nat.factorization L p : ℝ) * Real.log (p : ℝ) := by
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors p.property
  have hpdvd : (p : ℕ) ∣ L := Nat.dvd_of_mem_primeFactors p.property
  have hfac_pos : 0 < Nat.factorization L p := hp.factorization_pos_of_dvd hL hpdvd
  have hp_gt : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlog_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp_gt
  have hfac_cast_pos : 0 < (Nat.factorization L p : ℝ) := by exact_mod_cast hfac_pos
  nlinarith

private lemma xi_prime_phase_torus_dense_uniquely_ergodic_frequency_ratio_irrational {L : ℕ}
    (hL : L ≠ 0) {p q : L.primeFactors} (hpq : p ≠ q) :
    Irrational
      ((2 * (Nat.factorization L p : ℝ) * Real.log (p : ℝ)) /
        (2 * (Nat.factorization L q : ℝ) * Real.log (q : ℝ))) := by
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors p.property
  have hq : Nat.Prime q := Nat.prime_of_mem_primeFactors q.property
  have hp_nat_ne : (p : ℕ) ≠ q := by
    exact fun h => hpq (Subtype.ext h)
  have hp_fac_pos : 0 < Nat.factorization L p :=
    hp.factorization_pos_of_dvd hL (Nat.dvd_of_mem_primeFactors p.property)
  have hq_fac_pos : 0 < Nat.factorization L q :=
    hq.factorization_pos_of_dvd hL (Nat.dvd_of_mem_primeFactors q.property)
  have hp_log_pos : 0 < Real.log (p : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hp.one_lt)
  have hq_log_pos : 0 < Real.log (q : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hq.one_lt)
  have hp_fac_ne : (Nat.factorization L p : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hp_fac_pos
  have hq_fac_ne : (Nat.factorization L q : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hq_fac_pos
  have hp_log_ne : Real.log (p : ℝ) ≠ 0 := hp_log_pos.ne'
  have hq_log_ne : Real.log (q : ℝ) ≠ 0 := hq_log_pos.ne'
  have hlog_irr :
      Irrational (Real.log (p : ℝ) / Real.log (q : ℝ)) :=
    xi_prime_phase_torus_dense_uniquely_ergodic_prime_log_ratio_irrational hp hq hp_nat_ne
  rw [irrational_iff_ne_rational] at hlog_irr ⊢
  intro m n hn hratio
  have hcross :
      ((n : ℝ) * (Nat.factorization L p : ℝ)) * Real.log (p : ℝ) =
        ((m : ℝ) * (Nat.factorization L q : ℝ)) * Real.log (q : ℝ) := by
    have hratio' :
        (2 * (Nat.factorization L p : ℝ) * Real.log (p : ℝ)) /
            (2 * (Nat.factorization L q : ℝ) * Real.log (q : ℝ)) =
          (m : ℝ) / (n : ℝ) := by
      simpa using hratio
    field_simp [hp_fac_ne, hq_fac_ne, hp_log_ne, hq_log_ne, hn] at hratio'
    nlinarith
  have hden_ne : ((n : ℝ) * (Nat.factorization L p : ℝ)) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast hn) hp_fac_ne
  have hratio_log :
      Real.log (p : ℝ) / Real.log (q : ℝ) =
        ((m : ℝ) * (Nat.factorization L q : ℝ)) /
          ((n : ℝ) * (Nat.factorization L p : ℝ)) := by
    apply (div_eq_div_iff hq_log_ne hden_ne).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcross
  have hden_int_ne : n * (Nat.factorization L p : ℤ) ≠ 0 := by
    refine mul_ne_zero hn ?_
    exact_mod_cast Nat.ne_of_gt hp_fac_pos
  exact
    hlog_irr (m * (Nat.factorization L q : ℤ)) (n * (Nat.factorization L p : ℤ)) hden_int_ne <| by
      simpa [Int.cast_mul, Nat.cast_ofNat, mul_comm, mul_left_comm, mul_assoc] using hratio_log

/-- Concrete finite-prime-support package for the prime-phase torus flow. The prime-frequency
vector determines a compatible arithmetic-singular-ring subgroup and character, every two-prime
projection has irrational frequency ratio and hence dense additive closure, and the corresponding
two-coordinate observable projections are aperiodic. -/
def xi_prime_phase_torus_dense_uniquely_ergodic_statement (L : ℕ) : Prop :=
  let S := L.primeFactors
  let ω : S → ℝ := fun p => 2 * (Nat.factorization L p : ℝ) * Real.log (p : ℝ)
  Nonempty (Omega.CircleDimension.arithmeticSingularRingOneParameterSubgroups S) ∧
    Omega.CircleDimension.ArithmeticSingularRingPrimeFrequencyCharacterEval S ω ∧
    (∀ p q : S, p ≠ q → Irrational (ω p / ω q)) ∧
    (∀ p q : S, p ≠ q → Dense (AddSubgroup.closure {ω p, ω q} : Set ℝ)) ∧
    let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
    let α : Fin (Fintype.card S) → ℝ := fun j => ω (e.symm j)
    ∀ p q : S, p ≠ q →
      ¬ Omega.CircleDimension.PeriodicTorusRotationObservablePair α (e p) (e q)

/-- Paper label: `thm:xi-prime-phase-torus-dense-uniquely-ergodic`. The prime support of `L`
produces a concrete arithmetic-singular-ring frequency vector; distinct prime coordinates have
irrational frequency ratios by unique factorization of primes, so every two-prime projection is
dense, and the observable-closure dichotomy rules out periodic two-coordinate projections. -/
theorem paper_xi_prime_phase_torus_dense_uniquely_ergodic (L : ℕ) (hL : 2 ≤ L) :
    xi_prime_phase_torus_dense_uniquely_ergodic_statement L := by
  classical
  let S : Finset ℕ := L.primeFactors
  let ω : S → ℝ := fun p => 2 * (Nat.factorization L p : ℝ) * Real.log (p : ℝ)
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let α : Fin (Fintype.card S) → ℝ := fun j => ω (e.symm j)
  have hL_ne : L ≠ 0 := by omega
  have hClosure :=
    Omega.CircleDimension.paper_cdim_arithmetic_singular_ring_observable_closure_dichotomy
      (S := S) ω (Fintype.card S) α
  dsimp [xi_prime_phase_torus_dense_uniquely_ergodic_statement, S, ω, e, α]
  refine ⟨⟨Omega.CircleDimension.subgroupOfTorusFrequencyVector ω⟩, hClosure.1, ?_, ?_, ?_⟩
  · intro p q hpq
    simpa [ω] using
      xi_prime_phase_torus_dense_uniquely_ergodic_frequency_ratio_irrational hL_ne hpq
  · intro p q hpq
    rw [dense_addSubgroupClosure_pair_iff]
    simpa [ω] using
      xi_prime_phase_torus_dense_uniquely_ergodic_frequency_ratio_irrational hL_ne hpq
  · intro p q hpq
    have hωq_pos : 0 < ω q := by
      simpa [ω] using xi_prime_phase_torus_dense_uniquely_ergodic_frequency_pos hL_ne q
    have hαq_ne : α (e q) ≠ 0 := by
      simpa [α, e] using hωq_pos.ne'
    have hαirr : Irrational (α (e p) / α (e q)) := by
      simpa [α, e, ω] using
        xi_prime_phase_torus_dense_uniquely_ergodic_frequency_ratio_irrational hL_ne hpq
    exact hClosure.2.2 (e p) (e q) hαq_ne hαirr

end Omega.Zeta
