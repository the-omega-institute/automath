import Mathlib.Tactic

namespace Omega.POM

/-- Concrete truncation depth for the noncommutation witness. The retained prefix is assumed
nonempty so that a tail-triggered rewrite can alter visible data. -/
structure pom_truncation_not_commute_data where
  keep : ℕ
  keep_pos : 0 < keep

namespace pom_truncation_not_commute_data

/-- Boolean words of length `keep + 1`: a retained prefix of length `keep` together with one extra
tail bit that can trigger a fold rewrite. -/
abbrev word (D : pom_truncation_not_commute_data) := Fin (D.keep + 1) → Bool

/-- The retained prefix after truncation. -/
abbrev retainedPrefix (D : pom_truncation_not_commute_data) := Fin D.keep → Bool

/-- The visible prefix obtained by truncation. -/
def truncate (D : pom_truncation_not_commute_data) (w : D.word) : D.retainedPrefix :=
  fun i => w (Fin.castSucc i)

/-- The tail index whose bit triggers the fold rewrite on the visible prefix. -/
def triggerIndex (D : pom_truncation_not_commute_data) : Fin (D.keep + 1) :=
  ⟨D.keep, Nat.lt_succ_self D.keep⟩

/-- Folding after truncation sees no extra tail bit, so in this minimal model it leaves the
truncated prefix unchanged. -/
def truncate_then_fold (D : pom_truncation_not_commute_data) (w : D.word) : D.retainedPrefix :=
  D.truncate w

/-- Folding before restricting inspects the final tail bit. If that bit is `true`, the first
retained coordinate is toggled before the result is restricted to the visible prefix. -/
def fold_then_restrict (D : pom_truncation_not_commute_data) (w : D.word) : D.retainedPrefix :=
  fun i =>
    if _h0 : i.1 = 0 then
      if w D.triggerIndex then !(w (Fin.castSucc i)) else w (Fin.castSucc i)
    else
      w (Fin.castSucc i)

/-- The short witness word: all retained bits are `false`, while the extra tail bit is `true`. -/
def witnessWord (D : pom_truncation_not_commute_data) : D.word :=
  fun i => i = D.triggerIndex

/-- Paper-facing noncommutation statement. -/
def noncommuting_witness_exists (D : pom_truncation_not_commute_data) : Prop :=
  ∃ w : D.word, D.truncate_then_fold w ≠ D.fold_then_restrict w

end pom_truncation_not_commute_data

/-- Paper label: `prop:pom-truncation-not-commute`. The explicit word with only the final tail bit
set shows that folding before restriction toggles the first retained coordinate, whereas truncating
first removes the trigger and leaves the retained prefix unchanged. -/
theorem paper_pom_truncation_not_commute
    (D : pom_truncation_not_commute_data) : D.noncommuting_witness_exists := by
  refine ⟨D.witnessWord, ?_⟩
  intro hEq
  let i0 : Fin D.keep := ⟨0, D.keep_pos⟩
  have hi0 := congrFun hEq i0
  have hi0_zero : i0.1 = 0 := rfl
  have hcast_ne : Fin.castSucc i0 ≠ D.triggerIndex := by
    intro h
    exact (Nat.ne_of_lt i0.is_lt) (congrArg Fin.val h)
  have hw_prefix : D.witnessWord (Fin.castSucc i0) = false := by
    simp [pom_truncation_not_commute_data.witnessWord, hcast_ne]
  have hw_trigger : D.witnessWord D.triggerIndex = true := by
    simp [pom_truncation_not_commute_data.witnessWord]
  have hprefix_false : D.truncate_then_fold D.witnessWord i0 = false := by
    simp [pom_truncation_not_commute_data.truncate_then_fold,
      pom_truncation_not_commute_data.truncate, hw_prefix]
  have hfold_true : D.fold_then_restrict D.witnessWord i0 = true := by
    simp [pom_truncation_not_commute_data.fold_then_restrict, hi0_zero,
      hw_prefix, hw_trigger]
  rw [hprefix_false, hfold_true] at hi0
  contradiction

end Omega.POM
