import Mathlib.Analysis.SpecialFunctions.Exp

namespace Omega.POM

/-- Paper label: `thm:pom-toggle-odd-sector-exponential-thinness`. -/
theorem paper_pom_toggle_odd_sector_exponential_thinness {α : Type*} (Prob : (α → Prop) → ℝ)
    (N : α → ℕ) (m : ℕ) (ε c : ℝ) (scanOdd invOdd : α → Prop)
    (hmono : ∀ {A B : α → Prop}, (∀ x, A x → B x) → Prob A ≤ Prob B)
    (hscan : ∀ x, scanOdd x → N x ≤ 1) (hinv : ∀ x, invOdd x → N x ≤ 1)
    (hthreshold : ∀ x, N x ≤ 1 → (N x : ℝ) ≤ ε * (m : ℝ))
    (hldp : Prob (fun x => (N x : ℝ) ≤ ε * (m : ℝ)) ≤ Real.exp (-(c * (m : ℝ)))) :
    Prob scanOdd ≤ Real.exp (-(c * (m : ℝ))) ∧
      Prob invOdd ≤ Real.exp (-(c * (m : ℝ))) := by
  constructor
  · exact le_trans (hmono (fun x hx => hthreshold x (hscan x hx))) hldp
  · exact le_trans (hmono (fun x hx => hthreshold x (hinv x hx))) hldp

end Omega.POM
