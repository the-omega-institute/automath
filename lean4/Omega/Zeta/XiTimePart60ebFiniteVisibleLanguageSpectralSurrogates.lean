import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part60eb-finite-visible-language-spectral-surrogates`. -/
theorem paper_xi_time_part60eb_finite_visible_language_spectral_surrogates
    {Lang Audit Obj : Type*} (finiteSubLang : Lang → Prop) (completion : Obj → Prop)
    (encodes : Audit → Lang → Prop) (auditEquiv : Audit → Obj → Obj → Prop)
    (visibleEquiv : Lang → Obj → Obj → Prop) (globalPositive : Obj → Prop)
    (hcompress : ∀ L, finiteSubLang L → ∃ A, encodes A L)
    (hsurrogate :
      ∀ A, ∃ Xp Xm,
        completion Xp ∧ completion Xm ∧ auditEquiv A Xp Xm ∧
          globalPositive Xp ∧ ¬ globalPositive Xm)
    (hsound :
      ∀ {A L Xp Xm}, encodes A L → auditEquiv A Xp Xm → visibleEquiv L Xp Xm) :
    ∀ L, finiteSubLang L →
      ∃ Xp Xm,
        completion Xp ∧ completion Xm ∧ visibleEquiv L Xp Xm ∧
          globalPositive Xp ∧ ¬ globalPositive Xm := by
  intro L hL
  rcases hcompress L hL with ⟨A, henc⟩
  rcases hsurrogate A with ⟨Xp, Xm, hXp, hXm, haudit, hpos, hneg⟩
  exact ⟨Xp, Xm, hXp, hXm, hsound henc haudit, hpos, hneg⟩

end Omega.Zeta
