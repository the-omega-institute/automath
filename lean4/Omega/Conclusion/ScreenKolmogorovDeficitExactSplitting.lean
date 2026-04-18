import Mathlib

namespace Omega.Conclusion

theorem paper_conclusion_screen_kolmogorov_deficit_exact_splitting {V W : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] (f : V →ₗ[ZMod 2] W) :
    ∃ r : Nat, ∃ _h : V →ₗ[ZMod 2] (Fin r → ZMod 2),
      Nonempty (V ≃ₗ[ZMod 2] (LinearMap.range f × (Fin r → ZMod 2))) := by
  let r : Nat := Module.finrank (ZMod 2) (LinearMap.ker f)
  refine ⟨r, 0, ?_⟩
  have hdim :
      Module.finrank (ZMod 2) V =
        Module.finrank (ZMod 2) (LinearMap.range f × (Fin r → ZMod 2)) := by
    calc
      Module.finrank (ZMod 2) V =
          Module.finrank (ZMod 2) (LinearMap.range f) +
            Module.finrank (ZMod 2) (LinearMap.ker f) := by
            symm
            exact LinearMap.finrank_range_add_finrank_ker f
      _ = Module.finrank (ZMod 2) (LinearMap.range f) +
            Module.finrank (ZMod 2) (Fin r → ZMod 2) := by
            simp [r]
      _ = Module.finrank (ZMod 2) (LinearMap.range f × (Fin r → ZMod 2)) := by
            rw [Module.finrank_prod]
  exact ⟨LinearEquiv.ofFinrankEq
    (R := ZMod 2) (M := V) (M' := LinearMap.range f × (Fin r → ZMod 2)) hdim⟩

end Omega.Conclusion
