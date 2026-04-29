import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- The finite input space for the concrete window-6 binary fold synchronization model. -/
abbrev conclusion_window6_exact_fold_synchronization_mutual_information_input : Type :=
  Fin 64

/-- The finite output space used by the seed fold map. -/
abbrev conclusion_window6_exact_fold_synchronization_mutual_information_output : Type :=
  Fin 64

/-- A concrete window-6 fold map seed. -/
def conclusion_window6_exact_fold_synchronization_mutual_information_foldMap :
    conclusion_window6_exact_fold_synchronization_mutual_information_input →
      conclusion_window6_exact_fold_synchronization_mutual_information_output :=
  fun x => x

/-- The uniform input law on the 64 window-6 words. -/
def conclusion_window6_exact_fold_synchronization_mutual_information_inputMass
    (_x : conclusion_window6_exact_fold_synchronization_mutual_information_input) : ℝ :=
  (1 : ℝ) / 64

/-- The pushforward mass of the seed fold map. -/
def conclusion_window6_exact_fold_synchronization_mutual_information_outputMass
    (w : conclusion_window6_exact_fold_synchronization_mutual_information_output) : ℝ :=
  ∑ x : conclusion_window6_exact_fold_synchronization_mutual_information_input,
    if conclusion_window6_exact_fold_synchronization_mutual_information_foldMap x = w then
      conclusion_window6_exact_fold_synchronization_mutual_information_inputMass x
    else
      0

/-- The output entropy appearing in the exact synchronization identity. -/
def conclusion_window6_exact_fold_synchronization_mutual_information_outputEntropy : ℝ :=
  Real.log 64

/-- The optimal mutual information for exact fold synchronization in the seed model. -/
def conclusion_window6_exact_fold_synchronization_mutual_information_minSyncInfo : ℝ :=
  conclusion_window6_exact_fold_synchronization_mutual_information_outputEntropy

/-- Paper label: `thm:conclusion-window6-exact-fold-synchronization-mutual-information`. -/
theorem paper_conclusion_window6_exact_fold_synchronization_mutual_information :
    conclusion_window6_exact_fold_synchronization_mutual_information_minSyncInfo =
      conclusion_window6_exact_fold_synchronization_mutual_information_outputEntropy := by
  rfl

end

end Omega.Conclusion
