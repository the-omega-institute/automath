import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete witness data for the bad-prime analysis of a finite Hankel determinant family. The
witness determinants are the `content` scaled by the finitely many factors in `witnessScales`; the
distinguished scale `1` guarantees that the content itself is one of the witnesses. -/
structure XiHankelBadPrimeData where
  witnessScales : Finset ℤ
  content : ℤ
  one_mem_witnessScales : 1 ∈ witnessScales

namespace XiHankelBadPrimeData

/-- The finite set of witness determinants. -/
def witnessDeterminants (D : XiHankelBadPrimeData) : Finset ℤ :=
  D.witnessScales.image fun k => D.content * k

/-- Full rank modulo `p` means that some witness determinant stays nonzero modulo `p`. -/
def fullRankModPrime (D : XiHankelBadPrimeData) (p : ℕ) : Prop :=
  ∃ δ ∈ D.witnessDeterminants, ((δ : ℤ) : ZMod p) ≠ 0

/-- A bad prime is a prime at which every witness determinant vanishes modulo `p`. -/
def badPrime (D : XiHankelBadPrimeData) (p : ℕ) : Prop :=
  Nat.Prime p ∧ ¬ D.fullRankModPrime p

/-- Full rank modulo `p` is equivalent to the prime `p` not dividing the determinantal content. -/
def fullRankModPrimeIffPrimeNotDvdContent (D : XiHankelBadPrimeData) : Prop :=
  ∀ p : ℕ, Nat.Prime p → (D.fullRankModPrime p ↔ ¬ ((p : ℤ) ∣ D.content))

/-- The bad-prime set is exactly the set of prime divisors of the determinantal content. -/
def badPrimesExactlyPrimeDivisors (D : XiHankelBadPrimeData) : Prop :=
  ∀ p : ℕ, Nat.Prime p → (D.badPrime p ↔ ((p : ℤ) ∣ D.content))

/-- The determinantal content divides every witness determinant. -/
def contentDvdEveryWitness (D : XiHankelBadPrimeData) : Prop :=
  ∀ δ ∈ D.witnessDeterminants, D.content ∣ δ

lemma content_mem_witnessDeterminants (D : XiHankelBadPrimeData) :
    D.content ∈ D.witnessDeterminants := by
  refine Finset.mem_image.mpr ?_
  exact ⟨1, D.one_mem_witnessScales, by simp [witnessDeterminants]⟩

lemma fullRankModPrime_iff_not_dvd_content (D : XiHankelBadPrimeData) (p : ℕ) :
    D.fullRankModPrime p ↔ ¬ ((p : ℤ) ∣ D.content) := by
  constructor
  · intro hFull hDvd
    rcases hFull with ⟨δ, hδ, hδnz⟩
    rcases Finset.mem_image.mp hδ with ⟨k, -, rfl⟩
    have hzero : (((D.content : ℤ) : ZMod p) = 0) := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hDvd
    have : (((D.content * k : ℤ) : ZMod p) = 0) := by
      simp [hzero]
    exact hδnz this
  · intro hNotDvd
    refine ⟨D.content, D.content_mem_witnessDeterminants, ?_⟩
    intro hzero
    exact hNotDvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by simpa using hzero))

lemma content_dvd_every_witness (D : XiHankelBadPrimeData) :
    D.contentDvdEveryWitness := by
  intro δ hδ
  rcases Finset.mem_image.mp hδ with ⟨k, -, rfl⟩
  exact ⟨k, by simp [witnessDeterminants, mul_comm]⟩

end XiHankelBadPrimeData

open XiHankelBadPrimeData

/-- Define the determinantal content via the distinguished witness `content`, observe that full
rank modulo `p` is exactly the existence of a witness determinant that survives modulo `p`, and
translate this into the prime-divisor criterion for the bad-prime set. -/
theorem paper_xi_hankel_discriminant_unavoidable_bad_primes (D : XiHankelBadPrimeData) :
    D.fullRankModPrimeIffPrimeNotDvdContent ∧ D.badPrimesExactlyPrimeDivisors ∧
      D.contentDvdEveryWitness := by
  refine ⟨?_, ?_, D.content_dvd_every_witness⟩
  · intro p hp
    exact D.fullRankModPrime_iff_not_dvd_content p
  · intro p hp
    constructor
    · intro hBad
      by_contra hDvd
      exact hBad.2 ((D.fullRankModPrime_iff_not_dvd_content p).2 hDvd)
    · intro hDvd
      exact ⟨hp, fun hFull => (D.fullRankModPrime_iff_not_dvd_content p).1 hFull hDvd⟩

end Omega.Zeta
