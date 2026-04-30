import Omega.Zeta.XiTimePart60acbConstantFiberFreeGroupActionCriterion
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped Classical

/-- Paper label: `cor:conclusion-window6-schur-flattening-not-quotient`. -/
theorem paper_conclusion_window6_schur_flattening_not_quotient {X Y : Type*} [Fintype X]
    [Fintype Y] (f : Y → X) (hf : Function.Surjective f)
    (h2 : ∃ x : X, Fintype.card {y : Y // f y = x} = 2)
    (h3 : ∃ x : X, Fintype.card {y : Y // f y = x} = 3)
    (schurFlattening entropyGain concentrationDrop : Prop) :
    schurFlattening → entropyGain → concentrationDrop →
      ¬ ∃ (G : Type*) (_ : Group G) (_ : Fintype G) (_ : MulAction G Y),
        (∀ {g : G}, (∃ y : Y, g • y = y) → g = 1) ∧
          ∀ y y' : Y, ((∃ g : G, g • y = y') ↔ f y = f y') := by
  intro _hSchur _hEntropy _hConcentration hQuotient
  rcases h2 with ⟨x2, hx2⟩
  rcases h3 with ⟨x3, hx3⟩
  rcases
    (Omega.Zeta.paper_xi_time_part60acb_constant_fiber_free_group_action_criterion
      f hf).mp hQuotient with
    ⟨D, _hDpos, hD⟩
  have hD2 : D = 2 := (hD x2).symm.trans hx2
  have hD3 : D = 3 := (hD x3).symm.trans hx3
  omega

end Omega.Conclusion
