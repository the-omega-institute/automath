import Mathlib.Tactic

namespace Omega.Topos

variable {α : Type*}

/-- Abstract nullness: admitted but without a global section. -/
def Null (Adm Sec : α → Prop) (r : α) : Prop :=
  Adm r ∧ ¬ Sec r

/-- Local failure mode: admissible but not locally sectionable. -/
def NullLoc (Adm LocSec : α → Prop) (r : α) : Prop :=
  Adm r ∧ ¬ LocSec r

/-- Compatibility failure mode: local sections exist, but they do not fit together. -/
def NullCmp (Adm LocSec CompSec : α → Prop) (r : α) : Prop :=
  Adm r ∧ LocSec r ∧ ¬ CompSec r

/-- Gluing failure mode: compatible local sections exist, but there is no global section. -/
def NullGlue (Adm CompSec Sec : α → Prop) (r : α) : Prop :=
  Adm r ∧ CompSec r ∧ ¬ Sec r

/-- Exactly one of three propositions holds. -/
def ExactlyOne3 (P Q R : Prop) : Prop :=
  (P ∨ Q ∨ R) ∧ ¬ (P ∧ Q) ∧ ¬ (P ∧ R) ∧ ¬ (Q ∧ R)

theorem nullLoc_implies_null
    (Adm LocSec Sec : α → Prop) (r : α)
    (hsecLoc : ∀ {x : α}, Sec x → LocSec x) :
    NullLoc Adm LocSec r → Null Adm Sec r := by
  rintro ⟨hAdm, hNotLoc⟩
  refine ⟨hAdm, ?_⟩
  intro hSec
  exact hNotLoc (hsecLoc hSec)

theorem nullCmp_implies_null
    (Adm LocSec CompSec Sec : α → Prop) (r : α)
    (hsecComp : ∀ {x : α}, Sec x → CompSec x) :
    NullCmp Adm LocSec CompSec r → Null Adm Sec r := by
  rintro ⟨hAdm, _hLoc, hNotComp⟩
  refine ⟨hAdm, ?_⟩
  intro hSec
  exact hNotComp (hsecComp hSec)

theorem nullGlue_implies_null
    (Adm CompSec Sec : α → Prop) (r : α) :
    NullGlue Adm CompSec Sec r → Null Adm Sec r := by
  rintro ⟨hAdm, _hComp, hNotSec⟩
  exact ⟨hAdm, hNotSec⟩

theorem nullLoc_not_nullCmp
    (Adm LocSec CompSec : α → Prop) (r : α) :
    NullLoc Adm LocSec r → ¬ NullCmp Adm LocSec CompSec r := by
  rintro ⟨_hAdm, hNotLoc⟩ ⟨_hAdm', hLoc, _hNotComp⟩
  exact hNotLoc hLoc

theorem nullLoc_not_nullGlue
    (Adm LocSec CompSec Sec : α → Prop) (r : α)
    (hcompLoc : ∀ {x : α}, CompSec x → LocSec x) :
    NullLoc Adm LocSec r → ¬ NullGlue Adm CompSec Sec r := by
  rintro ⟨_hAdm, hNotLoc⟩ ⟨_hAdm', hComp, _hNotSec⟩
  exact hNotLoc (hcompLoc hComp)

theorem nullCmp_not_nullGlue
    (Adm LocSec CompSec Sec : α → Prop) (r : α) :
    NullCmp Adm LocSec CompSec r → ¬ NullGlue Adm CompSec Sec r := by
  rintro ⟨_hAdm, _hLoc, hNotComp⟩ ⟨_hAdm', hComp, _hNotSec⟩
  exact hNotComp hComp

/-- Paper-facing trichotomy seed for the three null modes. -/
theorem paper_null_trichotomy_seeds
    (Adm LocSec CompSec Sec : α → Prop) (r : α)
    [Decidable (LocSec r)] [Decidable (CompSec r)]
    (hcompLoc : ∀ {x : α}, CompSec x → LocSec x)
    (hsecComp : ∀ {x : α}, Sec x → CompSec x) :
    Null Adm Sec r ↔
      ExactlyOne3
        (NullLoc Adm LocSec r)
        (NullCmp Adm LocSec CompSec r)
        (NullGlue Adm CompSec Sec r) := by
  constructor
  · rintro ⟨hAdm, hNotSec⟩
    by_cases hLoc : LocSec r
    · by_cases hComp : CompSec r
      · refine ⟨Or.inr (Or.inr ?_), ?_, ?_, ?_⟩
        · exact ⟨hAdm, hComp, hNotSec⟩
        · intro h
          exact (nullLoc_not_nullCmp Adm LocSec CompSec r h.1) h.2
        · intro h
          exact (nullLoc_not_nullGlue Adm LocSec CompSec Sec r hcompLoc h.1) h.2
        · intro h
          exact (nullCmp_not_nullGlue Adm LocSec CompSec Sec r h.1) h.2
      · refine ⟨Or.inr (Or.inl ?_), ?_, ?_, ?_⟩
        · exact ⟨hAdm, hLoc, hComp⟩
        · intro h
          exact (nullLoc_not_nullCmp Adm LocSec CompSec r h.1) h.2
        · intro h
          exact (nullLoc_not_nullGlue Adm LocSec CompSec Sec r hcompLoc h.1) h.2
        · intro h
          exact (nullCmp_not_nullGlue Adm LocSec CompSec Sec r h.1) h.2
    · refine ⟨Or.inl ?_, ?_, ?_, ?_⟩
      · exact ⟨hAdm, hLoc⟩
      · intro h
        exact (nullLoc_not_nullCmp Adm LocSec CompSec r h.1) h.2
      · intro h
        exact (nullLoc_not_nullGlue Adm LocSec CompSec Sec r hcompLoc h.1) h.2
      · intro h
        exact (nullCmp_not_nullGlue Adm LocSec CompSec Sec r h.1) h.2
  · intro h
    rcases h.1 with hLoc | hCmp | hGlue
    · exact nullLoc_implies_null Adm LocSec Sec r (fun {x} hx => hcompLoc (hsecComp hx)) hLoc
    · exact nullCmp_implies_null Adm LocSec CompSec Sec r hsecComp hCmp
    · exact nullGlue_implies_null Adm CompSec Sec r hGlue

end Omega.Topos
