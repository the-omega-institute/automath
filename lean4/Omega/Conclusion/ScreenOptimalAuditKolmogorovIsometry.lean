import Mathlib

namespace Omega.Conclusion

theorem paper_conclusion_screen_optimal_audit_kolmogorov_isometry {V W : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] (f : V →ₗ[ZMod 2] W) :
    ∃ r : Nat,
      Nonempty (V ≃ₗ[ZMod 2] (LinearMap.range f × (Fin r → ZMod 2))) ∧
        ∀ b < r, ¬ Nonempty (V ≃ₗ[ZMod 2] (LinearMap.range f × (Fin b → ZMod 2))) := by
  let r : Nat := Module.finrank (ZMod 2) (LinearMap.ker f)
  refine ⟨r, ?_, ?_⟩
  · have hdim :
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
  · intro b hb hnonempty
    rcases hnonempty with ⟨e⟩
    have hsum :
        Module.finrank (ZMod 2) (LinearMap.range f) + r =
          Module.finrank (ZMod 2) (LinearMap.range f) + b := by
      calc
        Module.finrank (ZMod 2) (LinearMap.range f) + r
            = Module.finrank (ZMod 2) V := by
                simp [r, LinearMap.finrank_range_add_finrank_ker]
        _ = Module.finrank (ZMod 2) (LinearMap.range f × (Fin b → ZMod 2)) := by
              simpa using e.finrank_eq
        _ = Module.finrank (ZMod 2) (LinearMap.range f) + b := by
              rw [Module.finrank_prod, Module.finrank_fin_fun]
    have hrb : r = b := Nat.add_left_cancel hsum
    exact (Nat.ne_of_lt hb) hrb.symm

end Omega.Conclusion
