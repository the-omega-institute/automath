import Omega.LogicExpansionChain.ChoiceSpectrum
import Omega.LogicExpansionChain.ChoiceSpectrumSymmetryInvariance

namespace Omega.LogicExpansionChain

/-- Paper-facing fixed-point obstruction: if a symmetry swaps two distinct action classes, then no
selector between those two classes can be symmetry-invariant.
    thm:logic-expansion-choice-spectrum-no-definable-selector -/
theorem paper_logic_expansion_choice_spectrum_no_definable_selector
    {Observer State Action Formula : Type}
    (Enabled : Observer → State → Set Action)
    (Upd : Observer → Action → State → Set State)
    (Forces : Observer → State → Formula → Prop)
    (i : Observer) (p : State)
    (tau : ActionClass Enabled Upd Forces i p ≃ ActionClass Enabled Upd Forces i p)
    {A B : ActionClass Enabled Upd Forces i p}
    (hAB : A ≠ B)
    (hA : tau A = B)
    (hB : tau B = A) :
    ¬ ∃ choose : ActionClass Enabled Upd Forces i p,
      (choose = A ∨ choose = B) ∧ tau choose = choose := by
  rintro ⟨choose, hchoose, hfixed⟩
  rcases hchoose with hchoose | hchoose
  · have hEq : A = B := by
      calc
        A = choose := hchoose.symm
        _ = tau choose := by rw [hfixed]
        _ = tau A := by rw [hchoose]
        _ = B := hA
    exact hAB hEq
  · have hEq : A = B := by
      calc
        A = tau B := by rw [hB]
        _ = tau choose := by rw [hchoose]
        _ = choose := hfixed
        _ = B := hchoose
    exact hAB hEq

end Omega.LogicExpansionChain
