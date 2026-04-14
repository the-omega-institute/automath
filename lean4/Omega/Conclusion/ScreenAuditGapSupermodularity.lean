import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion.ScreenAuditGapSupermodularity

open Finset

variable {α : Type*} [DecidableEq α]

/--
Abstract corank-style audit gap attached to a bounded rank function.
This packages the arithmetic core of
`thm:conclusion-fixedresolution-screen-audit-gap-supermodularity`.
-/
def AuditGap (ρ : ℕ) (r : Finset α → ℕ) (s : Finset α) : ℕ :=
  ρ - r s

/--
Abstract deficit function `|S| - r(S)`.
This packages the arithmetic core of
`thm:conclusion-fixedresolution-screen-audit-gap-supermodularity`.
-/
def VisibilityDefect (r : Finset α → ℕ) (s : Finset α) : ℕ :=
  s.card - r s

/-- Equality case for the rank submodularity defect. -/
def ModularPair (r : Finset α → ℕ) (s t : Finset α) : Prop :=
  r s + r t = r (s ∩ t) + r (s ∪ t)

theorem auditGap_supermodular
    (ρ : ℕ) (r : Finset α → ℕ)
    (hρ : ∀ s, r s ≤ ρ)
    (hsub : ∀ s t, r (s ∩ t) + r (s ∪ t) ≤ r s + r t) :
    ∀ s t,
      AuditGap ρ r s + AuditGap ρ r t ≤
        AuditGap ρ r (s ∩ t) + AuditGap ρ r (s ∪ t) := by
  intro s t
  dsimp [AuditGap]
  have hs := hρ s
  have ht := hρ t
  have hi := hρ (s ∩ t)
  have hu := hρ (s ∪ t)
  have hst := hsub s t
  omega

theorem auditGap_eq_iff_modularPair
    (ρ : ℕ) (r : Finset α → ℕ)
    (hρ : ∀ s, r s ≤ ρ) :
    ∀ s t,
      AuditGap ρ r (s ∩ t) + AuditGap ρ r (s ∪ t) =
          AuditGap ρ r s + AuditGap ρ r t ↔
        ModularPair r s t := by
  intro s t
  dsimp [AuditGap, ModularPair]
  have hs := hρ s
  have ht := hρ t
  have hi := hρ (s ∩ t)
  have hu := hρ (s ∪ t)
  omega

theorem visibilityDefect_supermodular
    (r : Finset α → ℕ)
    (hrcard : ∀ s, r s ≤ s.card)
    (hsub : ∀ s t, r (s ∩ t) + r (s ∪ t) ≤ r s + r t) :
    ∀ s t,
      VisibilityDefect r s + VisibilityDefect r t ≤
        VisibilityDefect r (s ∩ t) + VisibilityDefect r (s ∪ t) := by
  intro s t
  dsimp [VisibilityDefect]
  have hs := hrcard s
  have ht := hrcard t
  have hi := hrcard (s ∩ t)
  have hu := hrcard (s ∪ t)
  have hcard := card_union_add_card_inter s t
  have hst := hsub s t
  omega

theorem visibilityDefect_eq_iff_modularPair
    (r : Finset α → ℕ)
    (hrcard : ∀ s, r s ≤ s.card) :
    ∀ s t,
      VisibilityDefect r (s ∩ t) + VisibilityDefect r (s ∪ t) =
          VisibilityDefect r s + VisibilityDefect r t ↔
        ModularPair r s t := by
  intro s t
  dsimp [VisibilityDefect, ModularPair]
  have hs := hrcard s
  have ht := hrcard t
  have hi := hrcard (s ∩ t)
  have hu := hrcard (s ∪ t)
  have hcard := card_union_add_card_inter s t
  omega

/--
Paper-facing seed theorem for
`thm:conclusion-fixedresolution-screen-audit-gap-supermodularity`.

The concrete screen/matroid objects are abstracted to a finite-set rank function `r`.
-/
theorem paper_conclusion_fixedresolution_screen_audit_gap_supermodularity_seeds
    (ρ : ℕ) (r : Finset α → ℕ)
    (hρ : ∀ s, r s ≤ ρ)
    (hrcard : ∀ s, r s ≤ s.card)
    (hsub : ∀ s t, r (s ∩ t) + r (s ∪ t) ≤ r s + r t) :
    (∀ s t,
        AuditGap ρ r s + AuditGap ρ r t ≤
          AuditGap ρ r (s ∩ t) + AuditGap ρ r (s ∪ t)) ∧
      ∀ s t,
        VisibilityDefect r s + VisibilityDefect r t ≤
          VisibilityDefect r (s ∩ t) + VisibilityDefect r (s ∪ t) := by
  constructor
  · intro s t
    exact auditGap_supermodular ρ r hρ hsub s t
  · intro s t
    exact visibilityDefect_supermodular r hrcard hsub s t

/--
Paper-facing package theorem for
`thm:conclusion-fixedresolution-screen-audit-gap-supermodularity`.
-/
theorem paper_conclusion_fixedresolution_screen_audit_gap_supermodularity_package
    (ρ : ℕ) (r : Finset α → ℕ)
    (hρ : ∀ s, r s ≤ ρ)
    (hrcard : ∀ s, r s ≤ s.card) :
    (∀ s t,
        AuditGap ρ r (s ∩ t) + AuditGap ρ r (s ∪ t) =
            AuditGap ρ r s + AuditGap ρ r t ↔
          ModularPair r s t) ∧
      ∀ s t,
        VisibilityDefect r (s ∩ t) + VisibilityDefect r (s ∪ t) =
            VisibilityDefect r s + VisibilityDefect r t ↔
          ModularPair r s t := by
  constructor
  · intro s t
    exact auditGap_eq_iff_modularPair ρ r hρ s t
  · intro s t
    exact visibilityDefect_eq_iff_modularPair r hrcard s t

end Omega.Conclusion.ScreenAuditGapSupermodularity
