import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Paper label:
`cor:xi-time-part9zn-window6-visible-module-simplicity-incompressibility`. -/
theorem paper_xi_time_part9zn_window6_visible_module_simplicity_incompressibility
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (T : (Fin 21 → ℂ) →ₗ[ℂ] W) (hT : T ≠ 0)
    (hIntertwines : ∀ f : (Fin 21 → ℂ) →ₗ[ℂ] (Fin 21 → ℂ),
      ∃ g : W →ₗ[ℂ] W, T.comp f = g.comp T) :
    Function.Injective T ∧ 21 ≤ Module.finrank ℂ W := by
  let V := Fin 21 → ℂ
  have hker_bot : LinearMap.ker T = ⊥ := by
    by_contra hne
    obtain ⟨x, hxker, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hx_coord : ∃ i : Fin 21, x i ≠ 0 := by
      by_contra h
      apply hxne
      ext i
      exact not_not.mp (not_exists.mp h i)
    obtain ⟨i, hxi⟩ := hx_coord
    have hker_all : ∀ y : V, y ∈ LinearMap.ker T := by
      intro y
      let f : V →ₗ[ℂ] V :=
        { toFun := fun z => (z i / x i) • y
          map_add' := by
            intro u v
            ext j
            change ((u i + v i) / x i) * y j = u i / x i * y j + v i / x i * y j
            field_simp [hxi]
          map_smul' := by
            intro c z
            ext j
            change (c * z i / x i) * y j = c * (z i / x i * y j)
            field_simp [hxi]
          }
      obtain ⟨g, hg⟩ := hIntertwines f
      have hfx : T (f x) = 0 := by
        have hcomp := LinearMap.congr_fun hg x
        simpa [LinearMap.mem_ker.mp hxker] using hcomp
      have hfx_eq : f x = y := by
        ext j
        change (x i / x i) * y j = y j
        field_simp [hxi]
      simpa [hfx_eq] using hfx
    have hker_top : LinearMap.ker T = ⊤ := Submodule.eq_top_iff'.mpr hker_all
    have hzero : T = 0 := by
      apply LinearMap.ext
      intro y
      have hy : y ∈ LinearMap.ker T := by
        rw [hker_top]
        trivial
      exact LinearMap.mem_ker.mp hy
    exact hT hzero
  have hinj : Function.Injective T := LinearMap.ker_eq_bot.mp hker_bot
  refine ⟨hinj, ?_⟩
  have hfin := LinearMap.finrank_le_finrank_of_injective (f := T) hinj
  simpa [Module.finrank_fin_fun] using hfin

end

end Omega.Zeta
