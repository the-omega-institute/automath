import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-elliptic-e3-2torsion-q6-branching`. -/
theorem paper_conclusion_elliptic_e3_2torsion_q6_branching :
    (Nonempty ((Fin 3 → Fin 2 → ZMod 2) ≃ (Fin 6 → ZMod 2))) ∧
      Fintype.card (Fin 3 → Fin 2 → ZMod 2) = 2 ^ 6 := by
  classical
  let e : (Fin 3 → Fin 2 → ZMod 2) ≃ (Fin 6 → ZMod 2) :=
    (Equiv.curry (Fin 3) (Fin 2) (ZMod 2)).symm.trans
      (finProdFinEquiv.arrowCongr (Equiv.refl (ZMod 2)))
  refine ⟨⟨e⟩, ?_⟩
  calc
    Fintype.card (Fin 3 → Fin 2 → ZMod 2) = Fintype.card (Fin 6 → ZMod 2) :=
      Fintype.card_congr e
    _ = 2 ^ 6 := by
      rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]

end Omega.Conclusion
