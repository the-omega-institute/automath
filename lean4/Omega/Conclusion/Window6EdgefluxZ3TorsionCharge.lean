import Mathlib.Algebra.Group.Prod
import Mathlib.Data.ZMod.Basic

namespace Omega.Conclusion

/-- Projecting an additive model of the window-6 edge-flux cokernel onto the unique `3`-primary
factor yields the paper's canonical three-valued torsion charge. The supplied additive equivalence
packages the Smith-form decomposition `ZMod 3 × ZMod 3450`, and the first projection is
surjective. -/
theorem paper_conclusion_window6_edgeflux_z3_torsion_charge
    (G : Type) [AddCommGroup G] (hG : Nonempty (G ≃+ (ZMod 3 × ZMod 3450))) :
    ∃ τ : G →+ ZMod 3, Function.Surjective τ := by
  rcases hG with ⟨e⟩
  refine ⟨(AddMonoidHom.fst (ZMod 3) (ZMod 3450)).comp e.toAddMonoidHom, ?_⟩
  intro a
  refine ⟨e.symm (a, 0), ?_⟩
  change (e (e.symm (a, 0))).1 = a
  exact congrArg Prod.fst (e.apply_symm_apply (a, 0))

end Omega.Conclusion
