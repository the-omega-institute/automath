import Mathlib.Tactic

namespace Omega.Conclusion

/-- The synchronized first-deviation depth is the common-agreement minimum across the three
branchwise depth profiles. -/
def conclusion_2adic_first_deviation_time_halting_depth_synchronized {α : Type*}
    (T₁ T₂ T₃ : α → WithTop ℕ) : α → WithTop ℕ :=
  fun x => min (T₁ x) (min (T₂ x) (T₃ x))

/-- A local undecidability witness for the first-deviation map: if one could decide whether the
synchronized depth is finite, then one could decide halting. -/
def conclusion_2adic_first_deviation_time_halting_depth_first_deviation_map_noncomputable
    {α : Type*} (T : α → WithTop ℕ) : Prop :=
  IsEmpty (DecidablePred (fun x => T x ≠ ⊤))

/-- Paper label: `prop:conclusion-2adic-first-deviation-time-halting-depth`.
If each of the three two-adic branches has the same first-deviation behavior, then their
synchronized first-deviation depth detects nonhalting, equals the halting depth on the halting
branch, and cannot be used to decide halting when halting itself is undecidable. -/
theorem paper_conclusion_2adic_first_deviation_time_halting_depth {α : Type*}
    (halts : α → Prop) (haltingDepth : α → ℕ) (L : ℕ)
    (T₁ T₂ T₃ : α → WithTop ℕ)
    (h₁_nonhalt : ∀ x, ¬ halts x ↔ T₁ x = ⊤)
    (h₂_nonhalt : ∀ x, ¬ halts x ↔ T₂ x = ⊤)
    (h₃_nonhalt : ∀ x, ¬ halts x ↔ T₃ x = ⊤)
    (h₁_halt : ∀ x, halts x → T₁ x = (L * haltingDepth x : ℕ))
    (h₂_halt : ∀ x, halts x → T₂ x = (L * haltingDepth x : ℕ))
    (h₃_halt : ∀ x, halts x → T₃ x = (L * haltingDepth x : ℕ))
    (hUndec : IsEmpty (DecidablePred halts)) :
    (∀ x,
      ¬ halts x ↔
        conclusion_2adic_first_deviation_time_halting_depth_synchronized T₁ T₂ T₃ x = ⊤) ∧
      (∀ x, halts x →
        conclusion_2adic_first_deviation_time_halting_depth_synchronized T₁ T₂ T₃ x =
          (L * haltingDepth x : ℕ)) ∧
      conclusion_2adic_first_deviation_time_halting_depth_first_deviation_map_noncomputable
        (conclusion_2adic_first_deviation_time_halting_depth_synchronized T₁ T₂ T₃) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      dsimp [conclusion_2adic_first_deviation_time_halting_depth_synchronized]
      rw [(h₁_nonhalt x).1 hx, (h₂_nonhalt x).1 hx, (h₃_nonhalt x).1 hx]
      simp
    · intro hx
      by_contra hhalts
      dsimp [conclusion_2adic_first_deviation_time_halting_depth_synchronized] at hx
      rw [h₁_halt x hhalts, h₂_halt x hhalts, h₃_halt x hhalts] at hx
      have hx' : ((L * haltingDepth x : ℕ) : WithTop ℕ) = ⊤ := by simpa using hx
      have hL : (L : WithTop ℕ) ≠ ⊤ := by simp
      have hD : (haltingDepth x : WithTop ℕ) ≠ ⊤ := by simp
      have hmul : ((L : WithTop ℕ) * (haltingDepth x : WithTop ℕ)) ≠ ⊤ :=
        WithTop.mul_ne_top hL hD
      exact hmul (by simpa using hx')
  · intro x hx
    dsimp [conclusion_2adic_first_deviation_time_halting_depth_synchronized]
    rw [h₁_halt x hx, h₂_halt x hx, h₃_halt x hx]
    simp
  · refine ⟨?_⟩
    intro hdec'
    apply hUndec.false
    intro x
    have hiff :
        halts x ↔
          conclusion_2adic_first_deviation_time_halting_depth_synchronized T₁ T₂ T₃ x ≠ ⊤ := by
      constructor
      · intro hx
        rw [show
          conclusion_2adic_first_deviation_time_halting_depth_synchronized T₁ T₂ T₃ x =
            (L * haltingDepth x : ℕ) by
              dsimp [conclusion_2adic_first_deviation_time_halting_depth_synchronized]
              rw [h₁_halt x hx, h₂_halt x hx, h₃_halt x hx]
              simp]
        have hL : (L : WithTop ℕ) ≠ ⊤ := by simp
        have hD : (haltingDepth x : WithTop ℕ) ≠ ⊤ := by simp
        exact WithTop.mul_ne_top hL hD
      · intro hx
        by_contra hnh
        exact hx <| by
          dsimp [conclusion_2adic_first_deviation_time_halting_depth_synchronized]
          rw [(h₁_nonhalt x).1 hnh, (h₂_nonhalt x).1 hnh, (h₃_nonhalt x).1 hnh]
          simp
    exact match hdec' x with
    | isTrue hs => isTrue (hiff.mpr hs)
    | isFalse hs => isFalse (fun hh => hs (hiff.mp hh))

end Omega.Conclusion
