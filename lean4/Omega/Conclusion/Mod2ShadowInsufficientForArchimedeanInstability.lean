import Mathlib.Tactic

namespace Omega.Conclusion

/-- The explicit mod-`2` shadow classes cited in the resonance window. -/
def conclusion_mod2_shadow_insufficient_for_archimedean_instability_shadowClass (q : ℕ) : Fin 2 :=
  if q = 12 ∨ q = 14 ∨ q = 16 then 0 else 1

/-- Integer-scaled archimedean instability witnesses from the resonance-window tables. -/
def conclusion_mod2_shadow_insufficient_for_archimedean_instability_score (q : ℕ) : ℕ :=
  if q = 12 then 22776615
  else if q = 14 then 28248141
  else if q = 16 then 33661669
  else if q = 13 then 25520014
  else if q = 15 then 30961823
  else 0

/-- An audit factors only through the mod-`2` shadow when it depends on `q` via the shadow class
alone. -/
def conclusion_mod2_shadow_insufficient_for_archimedean_instability_factorsThroughShadow
    {α : Type*} (audit : ℕ → α) : Prop :=
  ∃ lift : Fin 2 → α,
    ∀ q,
      audit q =
        lift (conclusion_mod2_shadow_insufficient_for_archimedean_instability_shadowClass q)

/-- Paper label: `cor:conclusion-mod2-shadow-insufficient-for-archimedean-instability`. The
resonance-window witnesses `q = 12, 14, 16` and `q = 13, 15` have identical mod-`2` shadow within
their class but different archimedean instability values, so no audit factoring only through that
shadow can reconstruct the instability score. -/
theorem paper_conclusion_mod2_shadow_insufficient_for_archimedean_instability :
    conclusion_mod2_shadow_insufficient_for_archimedean_instability_shadowClass 12 =
      conclusion_mod2_shadow_insufficient_for_archimedean_instability_shadowClass 14 ∧
    conclusion_mod2_shadow_insufficient_for_archimedean_instability_shadowClass 13 =
      conclusion_mod2_shadow_insufficient_for_archimedean_instability_shadowClass 15 ∧
    conclusion_mod2_shadow_insufficient_for_archimedean_instability_score 12 ≠
      conclusion_mod2_shadow_insufficient_for_archimedean_instability_score 14 ∧
    conclusion_mod2_shadow_insufficient_for_archimedean_instability_score 13 ≠
      conclusion_mod2_shadow_insufficient_for_archimedean_instability_score 15 ∧
    ∀ {α : Type*} (audit : ℕ → α),
      conclusion_mod2_shadow_insufficient_for_archimedean_instability_factorsThroughShadow audit →
        audit 12 = audit 14 ∧
        audit 13 = audit 15 ∧
        ¬ ∃ recover : α → ℕ,
          ∀ q,
            recover (audit q) =
              conclusion_mod2_shadow_insufficient_for_archimedean_instability_score q := by
  refine ⟨by simp [conclusion_mod2_shadow_insufficient_for_archimedean_instability_shadowClass], ?_,
    by simp [conclusion_mod2_shadow_insufficient_for_archimedean_instability_score], ?_⟩
  · simp [conclusion_mod2_shadow_insufficient_for_archimedean_instability_shadowClass]
  · refine ⟨by simp [conclusion_mod2_shadow_insufficient_for_archimedean_instability_score], ?_⟩
    intro α audit haudit
    rcases haudit with ⟨lift, hlift⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hlift 12, hlift 14]
      simp [conclusion_mod2_shadow_insufficient_for_archimedean_instability_shadowClass]
    · rw [hlift 13, hlift 15]
      simp [conclusion_mod2_shadow_insufficient_for_archimedean_instability_shadowClass]
    · rintro ⟨recover, hrecover⟩
      have haudit_eq : audit 12 = audit 14 := by
        rw [hlift 12, hlift 14]
        simp [conclusion_mod2_shadow_insufficient_for_archimedean_instability_shadowClass]
      have hscore_eq :
          conclusion_mod2_shadow_insufficient_for_archimedean_instability_score 12 =
            conclusion_mod2_shadow_insufficient_for_archimedean_instability_score 14 := by
        calc
          conclusion_mod2_shadow_insufficient_for_archimedean_instability_score 12 =
              recover (audit 12) := by symm; exact hrecover 12
          _ = recover (audit 14) := by rw [haudit_eq]
          _ = conclusion_mod2_shadow_insufficient_for_archimedean_instability_score 14 := hrecover 14
      simp [conclusion_mod2_shadow_insufficient_for_archimedean_instability_score] at hscore_eq

end Omega.Conclusion
