import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Folding.MaxFiber

namespace Omega.Conclusion

/-- Concrete audited-even window data for the minsector complement and its double-scale max-fiber
counterpart. -/
structure ConclusionMinsectorDoublescaleFeedbackLawData (m : Nat) where
  auditedWindow : m ∈ ({6, 8, 10, 12} : Finset Nat)
  totalCard : Nat
  minsectorCard : Nat
  totalCard_eq : totalCard = Nat.fib (m + 2)
  minsectorCard_eq : minsectorCard = Nat.fib m
  doublescaleMaxfiber_eq : Omega.X.maxFiberMultiplicity (2 * m - 2) = Nat.fib (m + 1)

/-- Complement left after removing the minimal-degeneracy sector. -/
def conclusion_minsector_doublescale_feedback_law_complementCard {m : Nat}
    (h : ConclusionMinsectorDoublescaleFeedbackLawData m) : Nat :=
  h.totalCard - h.minsectorCard

/-- The remaining complement is exactly the double-scale max-fiber count. -/
def ConclusionMinsectorDoublescaleFeedbackLawData.feedbackLaw {m : Nat}
    (h : ConclusionMinsectorDoublescaleFeedbackLawData m) : Prop :=
  (conclusion_minsector_doublescale_feedback_law_complementCard h =
      Omega.X.maxFiberMultiplicity (2 * m - 2)) ∧
    conclusion_minsector_doublescale_feedback_law_complementCard h = Nat.fib (m + 1)

/-- Paper label: `thm:conclusion-minsector-doublescale-feedback-law`. -/
theorem paper_conclusion_minsector_doublescale_feedback_law (m : Nat)
    (h : ConclusionMinsectorDoublescaleFeedbackLawData m) : h.feedbackLaw := by
  have _ := h.auditedWindow
  have hcomplement :
      conclusion_minsector_doublescale_feedback_law_complementCard h = Nat.fib (m + 1) := by
    dsimp [conclusion_minsector_doublescale_feedback_law_complementCard]
    rw [h.totalCard_eq, h.minsectorCard_eq, Nat.fib_add_two]
    omega
  refine ⟨?_, hcomplement⟩
  calc
    conclusion_minsector_doublescale_feedback_law_complementCard h = Nat.fib (m + 1) := hcomplement
    _ = Omega.X.maxFiberMultiplicity (2 * m - 2) := by
        symm
        exact h.doublescaleMaxfiber_eq

end Omega.Conclusion
