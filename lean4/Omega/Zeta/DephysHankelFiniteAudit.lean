import Omega.POM.MomentMinreal
import Omega.Zeta.HankelMaximalMinorSyndromeNormalFormUniqueness

namespace Omega.Zeta

open HankelMaximalMinorSyndromeData

/-- The first `2d` samples determine the principal and shifted `d × d` Hankel blocks. -/
theorem dephys_hankel_finite_audit_window_determines_hankel_blocks
    {k : Type*} [Field k] (a b : ℕ → k) (d : ℕ)
    (hwindow : ∀ n : ℕ, n < 2 * d → a n = b n) :
    hankelPrincipal a d = hankelPrincipal b d ∧ hankelShift a d = hankelShift b d := by
  refine ⟨?_, ?_⟩
  · ext i j
    exact hwindow (i.1 + j.1) (by omega)
  · ext i j
    exact hwindow (i.1 + j.1 + 1) (by omega)

/-- Concrete proposition packaging the finite-window Hankel audit: the first `2d` samples fix the
principal and shifted Hankel blocks, the maximal-minor syndrome normal form fixes the monic
recurrence and shift companion, and the moment/minimal-realization package identifies the
recovered recurrence order with the minimal realization dimension. -/
def dephys_hankel_finite_audit_statement : Prop :=
  (∀ {k : Type*} [Field k] (a b : ℕ → k) (d : ℕ),
      (∀ n : ℕ, n < 2 * d → a n = b n) →
        hankelPrincipal a d = hankelPrincipal b d ∧ hankelShift a d = hankelShift b d) ∧
    (∀ {k : Type*} [Field k] (D : HankelMaximalMinorSyndromeData k),
      D.kernelLineGeneratedBySyndrome ∧ D.monicRecurrenceUnique ∧ D.shiftCompanionAnnihilated) ∧
    (∀ D : Omega.POM.MomentMinrealData,
      D.hankelRank = D.recurrenceOrder ∧ D.minimalRealizationDim = D.recurrenceOrder)

/-- Verified finite-audit package assembled from the finite-window block-identification lemma, the
Hankel normal-form uniqueness theorem, and the minimal-realization wrapper. -/
theorem dephys_hankel_finite_audit_verified : dephys_hankel_finite_audit_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro k _ a b d hwindow
    exact dephys_hankel_finite_audit_window_determines_hankel_blocks a b d hwindow
  · intro k _ D
    exact paper_xi_hankel_maximal_minor_syndrome_normal_form_uniqueness D
  · intro D
    exact Omega.POM.paper_pom_moment_minreal D

/-- Paper label: `thm:dephys-hankel-finite-audit`.
The requested paper-facing name is the concrete proposition collecting the finite-window Hankel
audit consequences used in the dephysicalized horizon discussion. -/
def paper_dephys_hankel_finite_audit : Prop := by
  exact
    (∀ {k : Type*} [Field k] (a b : ℕ → k) (d : ℕ),
      (∀ n : ℕ, n < 2 * d → a n = b n) →
        hankelPrincipal a d = hankelPrincipal b d ∧ hankelShift a d = hankelShift b d) ∧
      (∀ {k : Type*} [Field k] (D : HankelMaximalMinorSyndromeData k),
        D.kernelLineGeneratedBySyndrome ∧ D.monicRecurrenceUnique ∧ D.shiftCompanionAnnihilated) ∧
      (∀ D : Omega.POM.MomentMinrealData,
        D.hankelRank = D.recurrenceOrder ∧ D.minimalRealizationDim = D.recurrenceOrder)

end Omega.Zeta
