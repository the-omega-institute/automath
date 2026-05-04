import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic

theorem paper_xi_time_part9n1d_prime_register_output_rank_threshold (r d : ℕ) :
    (∃ f : (Fin r → ℝ) →ₗ[ℝ] (Fin d → ℝ), Function.Surjective f) ↔ d ≤ r := by
  constructor
  · rintro ⟨f, hf⟩
    have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hf
    have hdimRange : Module.finrank ℝ (Fin d → ℝ) = Module.finrank ℝ (LinearMap.range f) := by
      rw [hrange, finrank_top]
    calc
      d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun (R := ℝ)).symm
      _ = Module.finrank ℝ (LinearMap.range f) := hdimRange
      _ ≤ Module.finrank ℝ (Fin r → ℝ) := LinearMap.finrank_range_le f
      _ = r := Module.finrank_fin_fun (R := ℝ)
  · intro hdr
    let f : (Fin r → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
      { toFun := fun x i => x ⟨i.1, lt_of_lt_of_le i.2 hdr⟩
        map_add' := by
          intro x y
          ext i
          rfl
        map_smul' := by
          intro c x
          ext i
          rfl }
    refine ⟨f, ?_⟩
    intro y
    refine ⟨fun j => if h : j.1 < d then y ⟨j.1, h⟩ else 0, ?_⟩
    ext i
    simp [f]
