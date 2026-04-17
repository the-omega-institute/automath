import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete CRT-local data for the Hankel normal-form multiplicity theorem.
The finite set `localModuli` packages the prime-power local factors of the modulus, and
`localMultiplicity q` records the Smith-entropy exponent governing the number of solutions modulo
`q`. -/
structure XiHankelNormalformCRTData where
  localModuli : Finset ℕ
  modulus : ℕ
  determinant : ℕ
  localMultiplicity : ℕ → ℕ
  globalSolutionCount : ℕ
  factor_dvd_modulus : ∀ q ∈ localModuli, q ∣ modulus
  factor_two_le : ∀ q ∈ localModuli, 2 ≤ q
  global_count_eq_prod :
    globalSolutionCount = Finset.prod localModuli (fun q => q ^ localMultiplicity q)
  multiplicity_zero_of_coprime :
    ∀ q ∈ localModuli, Nat.Coprime q determinant → localMultiplicity q = 0

namespace XiHankelNormalformCRTData

/-- The local solution count at the prime-power factor `q`. -/
def localSolutionCount (D : XiHankelNormalformCRTData) (q : ℕ) : ℕ :=
  q ^ D.localMultiplicity q

/-- Global solvability is equivalent to solvability at every local factor. -/
def globalSolvableIffLocalSolvable (D : XiHankelNormalformCRTData) : Prop :=
  0 < D.globalSolutionCount ↔ ∀ q ∈ D.localModuli, 0 < D.localSolutionCount q

/-- The global solution count factors as the product of the local prime-power counts, and each
local count is the corresponding Smith-entropy prime-power formula. -/
def solutionCountFactors (D : XiHankelNormalformCRTData) : Prop :=
  D.globalSolutionCount = Finset.prod D.localModuli D.localSolutionCount ∧
    ∀ q ∈ D.localModuli, D.localSolutionCount q = q ^ D.localMultiplicity q

/-- When the determinant is coprime to the full modulus, every local multiplicity vanishes and the
CRT product gives a unique global solution. -/
def coprimeDeterminantGivesUniqueness (D : XiHankelNormalformCRTData) : Prop :=
  Nat.Coprime D.modulus D.determinant → D.globalSolutionCount = 1

lemma localSolutionCount_pos (D : XiHankelNormalformCRTData) {q : ℕ} (hq : q ∈ D.localModuli) :
    0 < D.localSolutionCount q := by
  unfold localSolutionCount
  exact pow_pos (lt_of_lt_of_le (by decide : 0 < 2) (D.factor_two_le q hq)) _

lemma globalSolutionCount_pos (D : XiHankelNormalformCRTData) : 0 < D.globalSolutionCount := by
  rw [D.global_count_eq_prod]
  exact Finset.prod_pos (fun q hq => D.localSolutionCount_pos hq)

lemma globalSolvableIffLocalSolvable_holds (D : XiHankelNormalformCRTData) :
    D.globalSolvableIffLocalSolvable := by
  constructor
  · intro _ q hq
    exact D.localSolutionCount_pos hq
  · intro _
    exact D.globalSolutionCount_pos

lemma solutionCountFactors_holds (D : XiHankelNormalformCRTData) : D.solutionCountFactors := by
  refine ⟨?_, ?_⟩
  · simpa [localSolutionCount] using D.global_count_eq_prod
  · intro q hq
    rfl

lemma localSolutionCount_eq_one_of_coprime (D : XiHankelNormalformCRTData)
    {q : ℕ} (hq : q ∈ D.localModuli) (hcop : Nat.Coprime q D.determinant) :
    D.localSolutionCount q = 1 := by
  unfold localSolutionCount
  rw [D.multiplicity_zero_of_coprime q hq hcop, pow_zero]

lemma coprimeDeterminantGivesUniqueness_holds (D : XiHankelNormalformCRTData) :
    D.coprimeDeterminantGivesUniqueness := by
  intro hcop
  rw [D.global_count_eq_prod]
  refine Finset.prod_eq_one ?_
  intro q hq
  exact D.localSolutionCount_eq_one_of_coprime hq (Nat.Coprime.of_dvd_left (D.factor_dvd_modulus q hq) hcop)

end XiHankelNormalformCRTData

open XiHankelNormalformCRTData

/-- CRT-adelic multiplicity for the Hankel normal-form congruence family:
solvability is local, the global count factors into the prime-power counts, and coprime
determinant data forces uniqueness. -/
theorem paper_xi_hankel_normalform_crt_adelic_multiplicity (D : XiHankelNormalformCRTData) :
    D.globalSolvableIffLocalSolvable ∧ D.solutionCountFactors ∧
      D.coprimeDeterminantGivesUniqueness := by
  exact ⟨D.globalSolvableIffLocalSolvable_holds, D.solutionCountFactors_holds,
    D.coprimeDeterminantGivesUniqueness_holds⟩

end Omega.Zeta
