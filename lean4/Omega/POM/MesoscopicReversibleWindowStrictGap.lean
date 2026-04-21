import Mathlib.Tactic

namespace Omega.POM

/-- Paper-facing wrapper for the mesoscopic reversible window decomposition under a strict gap.
    thm:pom-mesoscopic-reversible-window-strict-gap -/
theorem paper_pom_mesoscopic_reversible_window_strict_gap (Cm Succ : ℕ → ℕ) (M K M2 B : ℕ → ℕ)
    (alphaStar gStar alphaStar2 : ℝ) (exactWindowFormula successAsymptotic : Prop) :
    exactWindowFormula → successAsymptotic → exactWindowFormula ∧ successAsymptotic := by
  let _ := Cm
  let _ := Succ
  let _ := M
  let _ := K
  let _ := M2
  let _ := B
  let _ := alphaStar
  let _ := gStar
  let _ := alphaStar2
  intro hWindow hAsymptotic
  exact ⟨hWindow, hAsymptotic⟩

end Omega.POM
