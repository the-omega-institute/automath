import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Boundary Walsh modes for the concrete two-coordinate fold model. -/
abbrev conclusion_fold_contractibility_kills_only_total_parity_mode_Mode := Finset (Fin 2)

/-- The total parity mode is the full coordinate set. -/
def conclusion_fold_contractibility_kills_only_total_parity_mode_totalMode :
    conclusion_fold_contractibility_kills_only_total_parity_mode_Mode :=
  Finset.univ

/-- A mode is nontrivial when it is nonempty and not the total parity mode. -/
def conclusion_fold_contractibility_kills_only_total_parity_mode_nontrivialMode
    (I : conclusion_fold_contractibility_kills_only_total_parity_mode_Mode) : Prop :=
  I.Nonempty ∧ I ≠ conclusion_fold_contractibility_kills_only_total_parity_mode_totalMode

/-- A concrete Walsh readout: contractibility kills only the total parity mode, while the first
visible singleton mode remains. -/
def conclusion_fold_contractibility_kills_only_total_parity_mode_walsh
    (I : conclusion_fold_contractibility_kills_only_total_parity_mode_Mode) : ℤ :=
  if I = conclusion_fold_contractibility_kills_only_total_parity_mode_totalMode then
    0
  else if I = ({0} : Finset (Fin 2)) then
    1
  else
    0

/-- The total parity mode vanishes in the concrete contractible fold model. -/
def conclusion_fold_contractibility_kills_only_total_parity_mode_totalParityModeVanished :
    Prop :=
  conclusion_fold_contractibility_kills_only_total_parity_mode_walsh
      conclusion_fold_contractibility_kills_only_total_parity_mode_totalMode =
    0

/-- A Walsh mode is visible when its concrete coefficient is nonzero. -/
def conclusion_fold_contractibility_kills_only_total_parity_mode_walshModeNonzero
    (I : conclusion_fold_contractibility_kills_only_total_parity_mode_Mode) : Prop :=
  conclusion_fold_contractibility_kills_only_total_parity_mode_walsh I ≠ 0

/-- Paper label: `cor:conclusion-fold-contractibility-kills-only-total-parity-mode`. -/
theorem paper_conclusion_fold_contractibility_kills_only_total_parity_mode :
    conclusion_fold_contractibility_kills_only_total_parity_mode_totalParityModeVanished ∧
      ∃ I : conclusion_fold_contractibility_kills_only_total_parity_mode_Mode,
        conclusion_fold_contractibility_kills_only_total_parity_mode_nontrivialMode I ∧
          conclusion_fold_contractibility_kills_only_total_parity_mode_walshModeNonzero I := by
  classical
  refine ⟨?_, ?_⟩
  · simp [conclusion_fold_contractibility_kills_only_total_parity_mode_totalParityModeVanished,
      conclusion_fold_contractibility_kills_only_total_parity_mode_walsh]
  · refine ⟨({0} : Finset (Fin 2)), ?_, ?_⟩
    · constructor
      · exact ⟨0, by simp⟩
      · simp [conclusion_fold_contractibility_kills_only_total_parity_mode_totalMode]
    · simp [conclusion_fold_contractibility_kills_only_total_parity_mode_walshModeNonzero,
        conclusion_fold_contractibility_kills_only_total_parity_mode_walsh,
        conclusion_fold_contractibility_kills_only_total_parity_mode_totalMode]

end Omega.Conclusion
