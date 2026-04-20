import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Polynomial

/-- Concrete coefficient data for the `u`-direction of the cyclotomic product.  The surviving
`u^(r n)` coefficients are packaged as polynomials in the auxiliary variable `z`, so the
compression polynomial in `U = u^r` is represented coefficientwise by `compressedCoeff`. -/
structure CharacterPhaseCyclotomicEliminationData where
  r : ℕ
  hr : 0 < r
  compressedCoeff : ℕ → Polynomial ℤ

namespace CharacterPhaseCyclotomicEliminationData

/-- The coefficient of `u^k` in the cyclotomic product obtained from the compressed
`U = u^r`-polynomial. -/
noncomputable def cyclotomicCoeff (D : CharacterPhaseCyclotomicEliminationData)
    (k : ℕ) : Polynomial ℤ :=
  if _ : D.r ∣ k then D.compressedCoeff (k / D.r) else 0

/-- Coefficientwise form of the `μ_r`-invariance consequence: only powers divisible by `r`
survive in the `u`-expansion. -/
def muInvariant (D : CharacterPhaseCyclotomicEliminationData) : Prop :=
  ∀ k, D.cyclotomicCoeff k ≠ 0 → D.r ∣ k

/-- Existence of the compression polynomial in `U = u^r`, encoded coefficientwise. -/
def existsCompression (D : CharacterPhaseCyclotomicEliminationData) : Prop :=
  ∃ F : ℕ → Polynomial ℤ, ∀ k, D.cyclotomicCoeff k = if D.r ∣ k then F (k / D.r) else 0

/-- Uniqueness of the coefficientwise `U = u^r` compression. -/
def uniqueCompression (D : CharacterPhaseCyclotomicEliminationData) : Prop :=
  ∀ F G : ℕ → Polynomial ℤ,
    (∀ k, D.cyclotomicCoeff k = if D.r ∣ k then F (k / D.r) else 0) →
    (∀ k, D.cyclotomicCoeff k = if D.r ∣ k then G (k / D.r) else 0) →
      F = G

end CharacterPhaseCyclotomicEliminationData

open CharacterPhaseCyclotomicEliminationData

/-- Coefficientwise cyclotomic elimination compresses the `u`-dependence to powers of `u^r`, and
the resulting compression polynomial is unique.
    prop:character-phase-cyclotomic-elimination -/
theorem paper_character_phase_cyclotomic_elimination
    (D : CharacterPhaseCyclotomicEliminationData) :
    D.muInvariant ∧ D.existsCompression ∧ D.uniqueCompression := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    by_contra hnot
    unfold CharacterPhaseCyclotomicEliminationData.cyclotomicCoeff at hk
    simp [hnot] at hk
  · refine ⟨D.compressedCoeff, ?_⟩
    intro k
    unfold CharacterPhaseCyclotomicEliminationData.cyclotomicCoeff
    by_cases hk : D.r ∣ k <;> simp [hk]
  · intro F G hF hG
    funext n
    have hdiv : D.r ∣ n * D.r := ⟨n, by simp [Nat.mul_comm]⟩
    have hFn0 : D.compressedCoeff (n * D.r / D.r) = F (n * D.r / D.r) := by
      simpa [CharacterPhaseCyclotomicEliminationData.cyclotomicCoeff, hdiv] using hF (n * D.r)
    have hGn0 : D.compressedCoeff (n * D.r / D.r) = G (n * D.r / D.r) := by
      simpa [CharacterPhaseCyclotomicEliminationData.cyclotomicCoeff, hdiv] using hG (n * D.r)
    have hdivEq : n * D.r / D.r = n := by
      rw [Nat.mul_comm, Nat.mul_div_right _ D.hr]
    have hFn : D.compressedCoeff n = F n := by
      simpa [hdivEq] using hFn0
    have hGn : D.compressedCoeff n = G n := by
      simpa [hdivEq] using hGn0
    exact hFn.symm.trans hGn

end Omega.SyncKernelWeighted
