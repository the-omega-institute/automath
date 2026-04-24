import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.DerivedTwoTermLaurentSingularRing

namespace Omega.CircleDimension

noncomputable section

/-- The rose Laurent lift has parameter singular ring determined by the critical equation of
`w ↦ (w^(d+n) + w^(d-n))/2`. Here we record the radius relation in the power form
`‖w‖^(2n) = (d-n)/(d+n)`. -/
def derived_rose_laurent_singular_ring_statement (d n : ℕ) : Prop :=
  ∀ w : ℂ, w ≠ 0 →
    Omega.UnitCirclePhaseArithmetic.twoTermLaurentDerivative
        (1 / 2 : ℂ) (1 / 2 : ℂ) (d + n) (d - n) w = 0 →
      w ^ (2 * n) = -((d - n : ℂ) / (d + n : ℂ))

/-- Paper label: `cor:derived-rose-laurent-singular-ring`. -/
theorem paper_derived_rose_laurent_singular_ring
    (d n : ℕ) (hn : 1 ≤ n) (hdn : n < d) :
    derived_rose_laurent_singular_ring_statement d n := by
  intro w hw hderiv
  have hsing :=
    Omega.UnitCirclePhaseArithmetic.paper_derived_two_term_laurent_singular_ring
      (1 / 2 : ℂ) (1 / 2 : ℂ) w (d + n) (d - n) hw (by norm_num) (by norm_num)
      (by omega) (by omega)
  have hexp : (d + n) - (d - n) = 2 * n := by omega
  have hratio :
      Omega.UnitCirclePhaseArithmetic.twoTermLaurentCriticalRatio
          (1 / 2 : ℂ) (1 / 2 : ℂ) (d + n) (d - n) =
        -((d - n : ℂ) / (d + n : ℂ)) := by
    have hd_pos : 0 < d := lt_of_le_of_lt (Nat.zero_le n) hdn
    have hden : ((d + n : ℂ)) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.add_pos_left hd_pos n))
    have hratio_eq :
        Omega.UnitCirclePhaseArithmetic.twoTermLaurentCriticalRatio
            (1 / 2 : ℂ) (1 / 2 : ℂ) (d + n) (d - n) =
          -((d - n : ℂ) / (d + n : ℂ)) := by
      have hdn_le : n ≤ d := Nat.le_of_lt hdn
      unfold Omega.UnitCirclePhaseArithmetic.twoTermLaurentCriticalRatio
      field_simp [hden]
      norm_num [Nat.cast_add, Nat.cast_sub hdn_le]
      ring
    exact hratio_eq
  have hcrit := (hsing.mp hderiv).1
  rw [hexp, hratio] at hcrit
  exact hcrit

end

end Omega.CircleDimension
