import Omega.Zeta.HankelMaximalMinorSyndromeNormalFormUniqueness

namespace Omega.Zeta

open Matrix
open scoped BigOperators

/-- Concrete package of offset-indexed Hankel maximal-minor data for a single sequence of rank
`d`. Each offset contributes a syndrome vector with nonzero principal determinant and a normalized
order-`d` recurrence for the same ambient sequence.

The theorem below shows that all these normalized recurrences agree, so every syndrome is the
corresponding principal determinant times one common monic coefficient vector. -/
structure HankelMaximalMinorSyndromeOffsetProjectiveInvarianceData
    (k : Type*) [Field k] where
  ι : Type*
  base : ι
  d : Nat
  a : Nat → k
  syndrome : ι → Fin (d + 1) → k
  shiftCompanion : ι → Matrix (Fin d) (Fin d) k
  principalDet : ι → k
  principalDet_ne_zero : ∀ i, principalDet i ≠ 0
  syndromeLast_eq_principalDet : ∀ i, syndrome i (Fin.last d) = principalDet i
  syndromeInKernel : ∀ i, (hankelExtended a d).mulVec (syndrome i) = 0
  kernelLine :
    ∀ i (x : Fin (d + 1) → k),
      (hankelExtended a d).mulVec x = 0 → ∃ c : k, x = c • syndrome i
  normalizedRecurrence : ∀ i, hankelRecurrence a (normalizedSyndrome (syndrome i))
  normalizedRecurrenceUnique :
    ∀ i (q : Fin (d + 1) → k),
      q (Fin.last d) = 1 →
        hankelRecurrence a q → q = normalizedSyndrome (syndrome i)
  shiftCompanion_spec : ∀ i, hankelPrincipal a d * shiftCompanion i = hankelShift a d
  shiftCompanion_annihilation :
    ∀ i, hankelRecurrenceEval (shiftCompanion i) (normalizedSyndrome (syndrome i)) = 0

namespace HankelMaximalMinorSyndromeOffsetProjectiveInvarianceData

variable {k : Type*} [Field k]

/-- The monic recurrence extracted from the maximal-minor syndrome does not depend on the chosen
invertible offset. -/
def normalizedRecurrenceIndependentOfOffset
    (D : HankelMaximalMinorSyndromeOffsetProjectiveInvarianceData k) : Prop :=
  ∀ i, normalizedSyndrome (D.syndrome i) = normalizedSyndrome (D.syndrome D.base)

/-- Every offset syndrome is the principal determinant at that offset times one common normalized
coefficient vector. -/
def offsetProjectiveInvariance
    (D : HankelMaximalMinorSyndromeOffsetProjectiveInvarianceData k) : Prop :=
  ∀ i, D.syndrome i = D.principalDet i • normalizedSyndrome (D.syndrome D.base)

theorem syndrome_eq_principalDet_smul_normalized
    (D : HankelMaximalMinorSyndromeOffsetProjectiveInvarianceData k) (i : D.ι) :
    D.syndrome i = D.principalDet i • normalizedSyndrome (D.syndrome i) := by
  ext j
  have hdet : D.principalDet i ≠ 0 := D.principalDet_ne_zero i
  have hmul : D.principalDet i * (D.syndrome i j / D.principalDet i) = D.syndrome i j := by
    field_simp [hdet]
  simpa [normalizedSyndrome, D.syndromeLast_eq_principalDet i] using hmul.symm

end HankelMaximalMinorSyndromeOffsetProjectiveInvarianceData

open HankelMaximalMinorSyndromeOffsetProjectiveInvarianceData

/-- Any two invertible offsets determine the same normalized order-`d` recurrence, and each
offset syndrome differs only by the scalar principal determinant.
    thm:xi-hankel-maximal-minor-syndrome-offset-projective-invariance -/
theorem paper_xi_hankel_maximal_minor_syndrome_offset_projective_invariance
    {k : Type*} [Field k] (D : HankelMaximalMinorSyndromeOffsetProjectiveInvarianceData k) :
    D.offsetProjectiveInvariance ∧ D.normalizedRecurrenceIndependentOfOffset := by
  have hBaseUnique :
      ∀ q : Fin (D.d + 1) → k,
        q (Fin.last D.d) = 1 →
          hankelRecurrence D.a q → q = normalizedSyndrome (D.syndrome D.base) :=
    D.normalizedRecurrenceUnique D.base
  have hMonicLast :
      ∀ i, normalizedSyndrome (D.syndrome i) (Fin.last D.d) = (1 : k) := by
    intro i
    have hdet : D.principalDet i ≠ 0 := D.principalDet_ne_zero i
    simp [normalizedSyndrome, D.syndromeLast_eq_principalDet i, hdet]
  have hIndependent : D.normalizedRecurrenceIndependentOfOffset := by
    intro i
    exact hBaseUnique (normalizedSyndrome (D.syndrome i)) (hMonicLast i) (D.normalizedRecurrence i)
  have hProjective : D.offsetProjectiveInvariance := by
    intro i
    calc
      D.syndrome i = D.principalDet i • normalizedSyndrome (D.syndrome i) :=
        D.syndrome_eq_principalDet_smul_normalized i
      _ = D.principalDet i • normalizedSyndrome (D.syndrome D.base) := by
        rw [hIndependent i]
  exact ⟨hProjective, hIndependent⟩

end Omega.Zeta
