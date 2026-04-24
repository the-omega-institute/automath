import Mathlib
import Omega.CircleDimension.CircleDim
import Omega.POM.CoprimeLedgerPrimorialOptimality

namespace Omega.CircleDimension

/-- Base-2 logarithm written using natural logarithms. -/
noncomputable def realLog2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/-- An injective prefix-plus-prime code into `2^b` binary prefixes and `P` prime-ledger residues
can carry at most `2^b * P` states. -/
theorem prefixPrime_code_card_bound {S : Type*} [Fintype S] (b P : ℕ)
    (hEnc : ∃ c : S → Fin (2 ^ b) × Fin P, Function.Injective c) :
    Fintype.card S ≤ 2 ^ b * P := by
  rcases hEnc with ⟨c, hc⟩
  simpa [Fintype.card_prod] using Fintype.card_le_of_injective c hc

private theorem realLog2_nat_mul_pow (b P : ℕ) (hP : 0 < P) :
    realLog2 (((2 ^ b) * P : ℕ) : ℝ) = b + realLog2 P := by
  unfold realLog2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have hpow_ne : ((2 : ℝ) ^ b) ≠ 0 := by positivity
  have hP_ne : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have hpow_log : Real.log ((2 : ℝ) ^ b) = (b : ℝ) * Real.log 2 := by
    rw [← Real.rpow_natCast, Real.log_rpow (by norm_num : 0 < (2 : ℝ))]
  have hlog_mul : Real.log ((2 : ℝ) ^ b * (P : ℝ)) = Real.log ((2 : ℝ) ^ b) + Real.log (P : ℝ) :=
    Real.log_mul hpow_ne hP_ne
  rw [Nat.cast_mul, Nat.cast_pow]
  calc
    Real.log ((2 : ℝ) ^ b * (P : ℝ)) / Real.log 2
        = (Real.log ((2 : ℝ) ^ b) + Real.log (P : ℝ)) / Real.log 2 := by rw [hlog_mul]
    _ = ((b : ℝ) * Real.log 2 + Real.log (P : ℝ)) / Real.log 2 := by rw [hpow_log]
    _ = b + Real.log (P : ℝ) / Real.log 2 := by
          field_simp [hlog2_ne]

private theorem realLog2_nat_cast_le_prefixPrime (m b P : ℕ) (hm : 0 < m) (hP : 0 < P)
    (h : m ≤ 2 ^ b * P) :
    realLog2 m ≤ b + realLog2 P := by
  have hm_real : 0 < (m : ℝ) := by exact_mod_cast hm
  have hbound : (m : ℝ) ≤ (((2 ^ b) * P : ℕ) : ℝ) := by exact_mod_cast h
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log hm_real hbound
  calc
    realLog2 m ≤ realLog2 ((((2 ^ b) * P : ℕ) : ℝ)) := by
      unfold realLog2
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hinv_nonneg : 0 ≤ (Real.log 2)⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_right hlog hinv_nonneg
    _ = b + realLog2 P := realLog2_nat_mul_pow b P hP

/-- Paper-facing prefix-prime ledger conservation inequality: the finite-set statement is the
cardinality bound for an injective code into a `2^b × P` alphabet, and any polynomial-growth lower
bound for a ball family lifts to the corresponding `log₂` ledger lower bound.
    thm:cdim-prefix-prime-ledger-conservation -/
theorem paper_cdim_prefix_prime_ledger_conservation
    {S : Type*} [Fintype S] (b P : ℕ)
    (hEnc : ∃ c : S → Fin (2 ^ b) × Fin P, Function.Injective c)
    {B : Type*} [Fintype B] [Nonempty B] (r N : ℕ)
    (hBallEnc : ∃ cN : B → Fin (2 ^ b) × Fin P, Function.Injective cN)
    (hP : 0 < P) :
    Fintype.card S ≤ 2 ^ b * P ∧
      ((∃ C : ℝ,
          (circleDim r 0 : ℝ) * realLog2 N - C ≤ realLog2 (Fintype.card B)) →
        ∃ C : ℝ, (b : ℝ) + realLog2 P ≥ (circleDim r 0 : ℝ) * realLog2 N - C) := by
  refine ⟨prefixPrime_code_card_bound b P hEnc, ?_⟩
  intro hGrowth
  rcases hGrowth with ⟨C, hGrowth⟩
  refine ⟨C, ?_⟩
  have hCard : Fintype.card B ≤ 2 ^ b * P :=
    prefixPrime_code_card_bound b P hBallEnc
  have hBpos : 0 < Fintype.card B := Fintype.card_pos_iff.mpr inferInstance
  have hUpper : realLog2 (Fintype.card B) ≤ (b : ℝ) + realLog2 P :=
    realLog2_nat_cast_le_prefixPrime (Fintype.card B) b P hBpos hP hCard
  linarith

/-- Specializing the prefix-prime ledger inequality to the squarefree primorial modulus
`P_k# = ∏_{j < k} p_j` yields the advertised ledger lower bound, and the standard Stirling lower
bound for the primorial logarithm supplies the growth estimate used in the support-count
discussion.
    `cor:cdim-squarefree-prime-support-growth` -/
theorem paper_cdim_squarefree_prime_support_growth
    {B : Type*} [Fintype B] [Nonempty B] (r N k : ℕ)
    (hBallEnc :
      ∃ cN : B → Fin (2 ^ 0) × Fin (Omega.POM.firstPrimeProduct k), Function.Injective cN)
    (hGrowth :
      ∃ C : ℝ, (circleDim r 0 : ℝ) * realLog2 N - C ≤ realLog2 (Fintype.card B)) :
    ∃ C : ℝ,
      (circleDim r 0 : ℝ) * realLog2 N - C ≤ realLog2 (Omega.POM.firstPrimeProduct k) ∧
        ((k + 1 : ℝ) * Real.log (k + 1) - (k + 1) +
            Real.log (k + 1) / 2 + Real.log (2 * Real.pi) / 2 ≤
          Real.log (Omega.POM.firstPrimeProduct k)) := by
  let unitEnc : Unit → Fin (2 ^ 0) × Fin (Omega.POM.firstPrimeProduct k) :=
    fun _ => ⟨⟨0, by decide⟩, ⟨0, Omega.POM.firstPrimeProduct_pos k⟩⟩
  have hEnc : ∃ c : Unit → Fin (2 ^ 0) × Fin (Omega.POM.firstPrimeProduct k), Function.Injective c :=
    ⟨unitEnc, by intro x y _; cases x; cases y; rfl⟩
  have hprefix :=
    paper_cdim_prefix_prime_ledger_conservation
      (S := Unit) 0 (Omega.POM.firstPrimeProduct k) hEnc r N hBallEnc
      (Omega.POM.firstPrimeProduct_pos k)
  rcases hprefix with ⟨_, hledger⟩
  rcases hledger hGrowth with ⟨C, hC⟩
  have hq : ∀ i : Fin k, 2 ≤ Omega.POM.nthPrime i := by
    intro i
    exact (Omega.POM.nthPrime_prime i).two_le
  have hpair : Pairwise fun i j : Fin k => Nat.Coprime (Omega.POM.nthPrime i) (Omega.POM.nthPrime j) :=
    by
      intro i j hij
      refine (Nat.coprime_primes (Omega.POM.nthPrime_prime i) (Omega.POM.nthPrime_prime j)).2 ?_
      intro hEq
      apply hij
      ext
      exact (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hEq
  have hprimorial :
      ((k + 1 : ℝ) * Real.log (k + 1) - (k + 1) +
          Real.log (k + 1) / 2 + Real.log (2 * Real.pi) / 2) ≤
        Real.log (Omega.POM.firstPrimeProduct k) :=
    (Omega.POM.paper_pom_coprime_ledger_primorial_optimality
      k 1 (fun i : Fin k => Omega.POM.nthPrime i) hq hpair).2.2
  exact ⟨C, by simpa using hC, hprimorial⟩

end Omega.CircleDimension
