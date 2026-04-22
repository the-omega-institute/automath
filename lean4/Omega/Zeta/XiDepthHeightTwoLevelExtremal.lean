import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-depth-height-two-level-extremal`. Two incommensurable address steps give
trivial intersection of the corresponding ambiguity lattices. -/
theorem paper_xi_depth_height_two_level_extremal (Delta Delta' : Real) (hDelta : Delta ≠ 0)
    (hDelta' : Delta' ≠ 0) (hirr : Irrational (Delta / Delta')) :
    (Set.range fun k : Int => (2 * Real.pi / Delta) * k) ∩
        (Set.range fun k : Int => (2 * Real.pi / Delta') * k) = ({0} : Set Real) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxDelta, hxDelta'⟩
    rcases hxDelta with ⟨m, hm⟩
    rcases hxDelta' with ⟨n, hn⟩
    by_cases hx0 : x = 0
    · simpa [hx0]
    · have hm0 : m ≠ 0 := by
        intro hm0
        have : x = 0 := by
          simpa [hm0] using hm.symm
        exact hx0 this
      have hn0 : n ≠ 0 := by
        intro hn0
        have : x = 0 := by
          simpa [hn0] using hn.symm
        exact hx0 this
      have hEq : (2 * Real.pi / Delta) * (m : ℝ) = (2 * Real.pi / Delta') * (n : ℝ) := by
        exact hm.trans hn.symm
      have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      have hcross : (m : ℝ) * Delta' = (n : ℝ) * Delta := by
        field_simp [hDelta, hDelta', htwoPi] at hEq
        linarith
      have hnReal0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
      have hratio : Delta / Delta' = (m : ℝ) / (n : ℝ) := by
        field_simp [hDelta', hnReal0]
        nlinarith [hcross]
      exact False.elim <| ((irrational_iff_ne_rational _).mp hirr) m n hn0 <| by
        simpa using hratio
  · intro hx
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    constructor <;> refine ⟨0, by simp⟩

end Omega.Zeta
