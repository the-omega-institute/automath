import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTimePart62eTripleProductAbelianizationC2Four

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part64a-four-quadratic-character-equidistribution`. -/
theorem paper_xi_time_part64a_four_quadratic_character_equidistribution
    (D : xi_time_part62e_triple_product_abelianization_c2_four_data)
    (boxDensity : (Fin 4 → ZMod 2) → ℚ)
    (hUniform :
      ∀ eps, boxDensity eps = 1 / (((2 : Nat) ^ D.abelianizationRank : Nat) : ℚ)) :
    ∀ eps, boxDensity eps = 1 / 16 := by
  intro eps
  have hrank := (paper_xi_time_part62e_triple_product_abelianization_c2_four D).1
  have h := hUniform eps
  rw [hrank] at h
  norm_num at h ⊢
  exact h

end Omega.Zeta
