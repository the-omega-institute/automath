import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-z2x2-sector-tqft-fourier-inversion`. -/
theorem paper_conclusion_z2x2_sector_tqft_fourier_inversion (sector : Bool → Bool → ℂ) :
    let twist : Bool → Bool → ℂ := fun s t =>
      ∑ a : Bool, ∑ b : Bool,
        (((if s && a then (-1 : ℂ) else 1) * (if t && b then (-1 : ℂ) else 1)) *
          sector a b)
    ∀ a b : Bool, sector a b =
      (1 / 4 : ℂ) * ∑ s : Bool, ∑ t : Bool,
        (((if s && a then (-1 : ℂ) else 1) * (if t && b then (-1 : ℂ) else 1)) *
          twist s t) := by
  dsimp
  intro a b
  cases a <;> cases b <;> simp <;> ring

end Omega.Conclusion
