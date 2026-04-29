import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Finite-codimensional interpolation on the critical line: one can annihilate the first `m`
functionals and normalize the last one to `1`. -/
def SelfdualScaleMellinFiniteCodimInterpolation {V : Type*} [AddCommGroup V] [Module ℝ V]
    (m : ℕ) (L : Fin (m + 1) → V →ₗ[ℝ] ℝ) : Prop :=
  ∃ w : V, (∀ j : Fin m, L (Fin.castSucc j) w = 0) ∧ L (Fin.last m) w = 1

/-- A finite linearly independent family of real linear functionals admits an interpolation vector
whose first `m` readings vanish and whose distinguished final reading is normalized to `1`.
    thm:conclusion-selfdual-scale-mellin-finite-codim-interpolation -/
theorem paper_conclusion_selfdual_scale_mellin_finite_codim_interpolation {V : Type*}
    [AddCommGroup V] [Module ℝ V] (m : ℕ) (L : Fin (m + 1) → V →ₗ[ℝ] ℝ)
    (hlin : LinearIndependent ℝ L) : SelfdualScaleMellinFiniteCodimInterpolation m L := by
  let W : Submodule ℝ (Module.Dual ℝ V) := Submodule.span ℝ (Set.range L)
  letI : FiniteDimensional ℝ W :=
    FiniteDimensional.of_injective hlin.repr (LinearMap.ker_eq_bot.mp hlin.repr_ker)
  let ψ : Module.Dual ℝ W :=
    { toFun := fun φ => hlin.repr φ (Fin.last m)
      map_add' := by
        intro φ χ
        exact congrArg (fun l : Fin (m + 1) →₀ ℝ => l (Fin.last m)) (hlin.repr.map_add φ χ)
      map_smul' := by
        intro c φ
        exact congrArg (fun l : Fin (m + 1) →₀ ℝ => l (Fin.last m)) (hlin.repr.map_smul c φ) }
  obtain ⟨q, hq⟩ := (Subspace.quotDualCoannihilatorToDual_bijective (W := W)).2 ψ
  obtain ⟨w, rfl⟩ := (Submodule.Quotient.mk_surjective (p := W.dualCoannihilator)) q
  refine ⟨w, ?_, ?_⟩
  · intro j
    let xj : W := ⟨L (Fin.castSucc j), Submodule.subset_span ⟨Fin.castSucc j, rfl⟩⟩
    have hrepr : hlin.repr xj = Finsupp.single (Fin.castSucc j) 1 := by
      apply hlin.repr_eq_single
      rfl
    have hEval : L (Fin.castSucc j) w = ψ xj := by
      simpa [xj, Submodule.quotDualCoannihilatorToDual_apply] using
        congrArg (fun F : Module.Dual ℝ W => F xj) hq
    rw [show ψ xj = 0 by simp [ψ, hrepr, Fin.castSucc_ne_last]] at hEval
    exact hEval
  · have hEval :=
      let xLast : W := ⟨L (Fin.last m), Submodule.subset_span ⟨Fin.last m, rfl⟩⟩
      congrArg (fun F : Module.Dual ℝ W => F xLast) hq
    let xLast : W := ⟨L (Fin.last m), Submodule.subset_span ⟨Fin.last m, rfl⟩⟩
    have hrepr : hlin.repr xLast = Finsupp.single (Fin.last m) 1 := by
      apply hlin.repr_eq_single
      rfl
    have hEval' : L (Fin.last m) w = ψ xLast := by
      simpa [xLast, Submodule.quotDualCoannihilatorToDual_apply] using hEval
    simpa [ψ, hrepr] using hEval'

end Omega.Conclusion
