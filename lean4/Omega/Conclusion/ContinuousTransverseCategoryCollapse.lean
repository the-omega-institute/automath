import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The single radial axis used by continuous transverse registers. -/
noncomputable def conclusion_continuous_transverse_category_collapse_radial_map
    (u : ℂ) : ℝ :=
  Real.log ‖u‖

/-- The coordinatewise finite product embedding attached to a family of radial factors. -/
def conclusion_continuous_transverse_category_collapse_product_embedding
    {k : ℕ} {Y : Fin k → Type*} (ψ : ∀ j : Fin k, ℝ → Y j) :
    ℝ → ∀ j : Fin k, Y j :=
  fun x j => ψ j x

/-- Paper label: `thm:conclusion-continuous-transverse-category-collapse`.  Every finite family
of registers that factors through the radial axis has a joint register factoring through the same
axis; if one coordinate factor is injective, the coordinatewise product factor is injective. -/
def conclusion_continuous_transverse_category_collapse_statement : Prop :=
  ∀ (k : ℕ) (Y : Fin k → Type*) (r : ∀ j : Fin k, ℂ → Y j)
      (ψ : ∀ j : Fin k, ℝ → Y j),
    (∀ j u, r j u = ψ j (conclusion_continuous_transverse_category_collapse_radial_map u)) →
      (∃ j0 : Fin k, Function.Injective (ψ j0)) →
        ∃ Ψ : ℝ → ∀ j : Fin k, Y j,
          Function.Injective Ψ ∧
            (∀ u : ℂ, (fun j : Fin k => r j u) =
              Ψ (conclusion_continuous_transverse_category_collapse_radial_map u))

theorem paper_conclusion_continuous_transverse_category_collapse :
    conclusion_continuous_transverse_category_collapse_statement := by
  intro k Y r ψ hfactor hinj
  rcases hinj with ⟨j0, hψ⟩
  refine ⟨conclusion_continuous_transverse_category_collapse_product_embedding ψ, ?_, ?_⟩
  · intro x y hxy
    exact hψ (congrFun hxy j0)
  · intro u
    funext j
    exact hfactor j u

end

end Omega.Conclusion
