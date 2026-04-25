import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete ambiguity-shell package for the localization theorem. The shell has a finite height
and carries an already synchronized zeta factor; the ambiguity tail below is the finite prefix
indicator cut off at that height. -/
structure conclusion_ambiguity_shell_preperiodic_localization_data where
  conclusion_ambiguity_shell_preperiodic_localization_window : ℕ
  conclusion_ambiguity_shell_preperiodic_localization_zetaSync : ℚ → ℚ

namespace conclusion_ambiguity_shell_preperiodic_localization_data

/-- The ambiguity shell has one terminal level and `window` transient levels. -/
def ambiguityLevelBound (D : conclusion_ambiguity_shell_preperiodic_localization_data) : ℕ :=
  D.conclusion_ambiguity_shell_preperiodic_localization_window + 1

/-- The nilpotent block contributes only before the shell-height cutoff. -/
def ambiguityBlockPower (D : conclusion_ambiguity_shell_preperiodic_localization_data)
    (n : ℕ) : ℚ :=
  if n < D.ambiguityLevelBound then 1 else 0

/-- The finite-prefix ambiguity tail. -/
def ambiguityTailWeight (D : conclusion_ambiguity_shell_preperiodic_localization_data)
    (n : ℕ) : ℚ :=
  D.ambiguityBlockPower n

/-- The shell transition strictly drops the level until it reaches the terminal level. -/
def ambiguityStep (D : conclusion_ambiguity_shell_preperiodic_localization_data)
    (i : Fin D.ambiguityLevelBound) : Fin D.ambiguityLevelBound :=
  if h : i.1 = 0 then ⟨0, by simp [ambiguityLevelBound]⟩ else ⟨i.1 - 1, by
    have hi : i.1 < D.ambiguityLevelBound := i.2
    have hpos : 0 < i.1 := Nat.pos_of_ne_zero h
    omega⟩

/-- Nilpotence of the ambiguity block at the shell height. -/
def nilpotentAtWindow (D : conclusion_ambiguity_shell_preperiodic_localization_data) : Prop :=
  D.ambiguityBlockPower D.ambiguityLevelBound = 0

/-- The shell has no nonterminal fixed periodic step. -/
def noNonterminalPeriodicStep
    (D : conclusion_ambiguity_shell_preperiodic_localization_data) : Prop :=
  ∀ i : Fin D.ambiguityLevelBound, i.1 ≠ 0 → D.ambiguityStep i ≠ i

/-- All ambiguity contribution is contained in the finite prefix. -/
def finitePrefixLocalized
    (D : conclusion_ambiguity_shell_preperiodic_localization_data) : Prop :=
  ∀ n : ℕ, D.ambiguityLevelBound ≤ n → D.ambiguityTailWeight n = 0

/-- The ambiguity factor is the synchronized zeta factor after the nilpotent tail vanishes. -/
def localizedZeta
    (D : conclusion_ambiguity_shell_preperiodic_localization_data) (z : ℚ) : ℚ :=
  D.conclusion_ambiguity_shell_preperiodic_localization_zetaSync z *
    (1 + D.ambiguityTailWeight D.ambiguityLevelBound)

/-- Zeta equality after the finite ambiguity prefix has been removed. -/
def zetaEquality (D : conclusion_ambiguity_shell_preperiodic_localization_data) : Prop :=
  ∀ z : ℚ, D.localizedZeta z =
    D.conclusion_ambiguity_shell_preperiodic_localization_zetaSync z

/-- Paper-facing localization conclusion: nilpotence, no nonterminal shell cycles, zeta equality,
and finite-prefix localization. -/
def preperiodicLocalized
    (D : conclusion_ambiguity_shell_preperiodic_localization_data) : Prop :=
  D.nilpotentAtWindow ∧ D.noNonterminalPeriodicStep ∧ D.zetaEquality ∧ D.finitePrefixLocalized

end conclusion_ambiguity_shell_preperiodic_localization_data

/-- Paper label: `thm:conclusion-ambiguity-shell-preperiodic-localization`. The finite ambiguity
tail is the nilpotent prefix indicator, so it vanishes at and after the shell height; the dropping
DAG step has no nonterminal fixed cycle, and the zeta factor reduces to the synchronized one. -/
theorem paper_conclusion_ambiguity_shell_preperiodic_localization
    (D : conclusion_ambiguity_shell_preperiodic_localization_data) : D.preperiodicLocalized := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [conclusion_ambiguity_shell_preperiodic_localization_data.nilpotentAtWindow,
      conclusion_ambiguity_shell_preperiodic_localization_data.ambiguityBlockPower]
  · intro i hi hfix
    have hval : (D.ambiguityStep i).1 = i.1 := by rw [hfix]
    unfold conclusion_ambiguity_shell_preperiodic_localization_data.ambiguityStep at hval
    split at hval
    · contradiction
    · rename_i hnonzero
      have hpos : 0 < i.1 := Nat.pos_of_ne_zero hnonzero
      have hsub : i.1 - 1 = i.1 := by simpa using hval
      omega
  · intro z
    simp [conclusion_ambiguity_shell_preperiodic_localization_data.localizedZeta,
      conclusion_ambiguity_shell_preperiodic_localization_data.ambiguityTailWeight,
      conclusion_ambiguity_shell_preperiodic_localization_data.ambiguityBlockPower]
  · intro n hn
    simp [conclusion_ambiguity_shell_preperiodic_localization_data.ambiguityTailWeight,
      conclusion_ambiguity_shell_preperiodic_localization_data.ambiguityBlockPower,
      not_lt.mpr hn]

end Omega.Conclusion
