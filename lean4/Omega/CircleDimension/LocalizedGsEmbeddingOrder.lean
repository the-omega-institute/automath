import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Concrete data for the finite-prime localization embedding order. The finite sets `S` and `T`
record the prime denominators allowed in the localizations `G_S = ℤ[S⁻¹]` and `G_T = ℤ[T⁻¹]`. -/
structure LocalizedGsEmbeddingOrderData where
  S : Finset ℕ
  T : Finset ℕ
  S_primes : ∀ p ∈ S, p.Prime
  T_primes : ∀ p ∈ T, p.Prime

namespace LocalizedGsEmbeddingOrderData

/-- A rational lies in `G_S` exactly when every prime divisor of its reduced denominator belongs
to `S`. -/
def inLocalizedGs (S : Finset ℕ) (q : ℚ) : Prop :=
  ∀ p, p.Prime → p ∣ q.den → p ∈ S

/-- An additive embedding `G_S ↪ G_T` inside `ℚ` is represented by multiplication by a nonzero
scalar `c = φ(1)`. -/
def localizedEmbedding (S T : Finset ℕ) : Prop :=
  ∃ c : ℚ, c ≠ 0 ∧ ∀ q, inLocalizedGs S q → inLocalizedGs T (c * q)

/-- The Pontryagin-dual surjection is tracked contravariantly by the same discrete-side scaling
embedding data. -/
def compatibleDualSurjection (S T : Finset ℕ) : Prop :=
  localizedEmbedding S T

/-- Paper-facing package: embeddings `G_S ↪ G_T` and compatible dual surjections
`Σ_T ↠ Σ_S` both occur exactly when `S ⊆ T`.
    thm:cdim-localized-gs-embedding-order -/
def package (D : LocalizedGsEmbeddingOrderData) : Prop :=
  (localizedEmbedding D.S D.T ↔ D.S ⊆ D.T) ∧
    (compatibleDualSurjection D.S D.T ↔ D.S ⊆ D.T)

lemma one_mem (S : Finset ℕ) : inLocalizedGs S 1 := by
  intro p hp hdiv
  exact False.elim (hp.not_dvd_one hdiv)

lemma inv_prime_pow_mem (S : Finset ℕ) {p : ℕ} (hp : p.Prime) (hS : p ∈ S) (n : ℕ) :
    inLocalizedGs S (((p ^ n : ℕ) : ℚ)⁻¹) := by
  intro q hq hqden
  rw [Rat.inv_natCast_den_of_pos (pow_pos hp.pos n)] at hqden
  have hqp_dvd : q ∣ p := hq.dvd_of_dvd_pow hqden
  have hqp : q = p := by
    rcases (Nat.dvd_prime hp).mp hqp_dvd with hq1 | hqp
    · exact False.elim (hq.ne_one hq1)
    · exact hqp
  simpa [hqp] using hS

lemma localizedEmbedding_of_subset {S T : Finset ℕ} (hST : S ⊆ T) :
    localizedEmbedding S T := by
  refine ⟨1, one_ne_zero, ?_⟩
  intro q hq p hp hdiv
  exact hST (hq p hp (by simpa using hdiv))

lemma subset_of_localizedEmbedding (D : LocalizedGsEmbeddingOrderData) :
    localizedEmbedding D.S D.T → D.S ⊆ D.T := by
  rintro ⟨c, hc0, hmap⟩ p hpS
  have hp : p.Prime := D.S_primes p hpS
  by_contra hpT
  let n := c.num.natAbs.factorization p + 1
  let q : ℚ := c * (((p ^ n : ℕ) : ℚ)⁻¹)
  have hq_mem : inLocalizedGs D.T q := by
    apply hmap
    exact inv_prime_pow_mem D.S hp hpS n
  have hp_not_dvd_qden : ¬ p ∣ q.den := by
    intro hpq
    exact hpT (hq_mem p hp hpq)
  have hcnum_ne_zero : c.num ≠ 0 := by
    intro hcnum
    exact hc0 (Rat.zero_of_num_zero hcnum)
  have hcnum_natAbs_ne_zero : c.num.natAbs ≠ 0 := by
    exact Int.natAbs_ne_zero.mpr hcnum_ne_zero
  have hmul :
      (c.num : ℤ) * q.den =
        q.num * c.den * (p ^ n : ℕ) := by
    dsimp [q, n]
    have hsign :
        (((p : ℤ) ^ (c.num.natAbs.factorization p + 1))).sign = 1 := by
      exact Int.sign_eq_one_of_pos (pow_pos (by exact_mod_cast hp.pos) _)
    simpa [Rat.inv_natCast_num, Rat.inv_natCast_den_of_pos (pow_pos hp.pos _), hsign, hp.ne_zero,
      mul_comm, mul_left_comm, mul_assoc]
      using
      (Rat.mul_num_den' c (((p ^ (c.num.natAbs.factorization p + 1) : ℕ) : ℚ)⁻¹)).symm
  have hdiv_prod : p ^ n ∣ c.num.natAbs * q.den := by
    refine ⟨Int.natAbs (q.num * c.den), ?_⟩
    have hmul_abs := congrArg Int.natAbs hmul
    simpa [Int.natAbs_mul, mul_comm, mul_left_comm, mul_assoc] using hmul_abs
  have hfactor_qden : q.den.factorization p = 0 := by
    exact Nat.factorization_eq_zero_of_not_dvd hp_not_dvd_qden
  have hpow_le :
      n ≤ (c.num.natAbs * q.den).factorization p := by
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp
      (Nat.mul_ne_zero hcnum_natAbs_ne_zero q.den_ne_zero)).mp hdiv_prod
  have hfactor_mul :
      (c.num.natAbs * q.den).factorization p =
        c.num.natAbs.factorization p + q.den.factorization p := by
    rw [Nat.factorization_mul hcnum_natAbs_ne_zero q.den_ne_zero, Finsupp.add_apply]
  dsimp [n] at hpow_le
  rw [hfactor_mul, hfactor_qden, add_zero] at hpow_le
  omega

end LocalizedGsEmbeddingOrderData

open LocalizedGsEmbeddingOrderData

set_option maxHeartbeats 400000 in
/-- Finite-prime localizations are ordered by inclusion of the allowed prime denominators:
inside `ℚ`, a scaling embedding `G_S ↪ G_T` exists exactly when `S ⊆ T`, and the compatible
Pontryagin-dual surjection `Σ_T ↠ Σ_S` is the contravariant companion of the same order relation.
    thm:cdim-localized-gs-embedding-order -/
theorem paper_cdim_localized_gs_embedding_order (D : LocalizedGsEmbeddingOrderData) : D.package := by
  have hMain : localizedEmbedding D.S D.T ↔ D.S ⊆ D.T := by
    constructor
    · exact D.subset_of_localizedEmbedding
    · intro hST
      exact localizedEmbedding_of_subset hST
  exact ⟨hMain, by simpa [LocalizedGsEmbeddingOrderData.compatibleDualSurjection] using hMain⟩

end Omega.CircleDimension
