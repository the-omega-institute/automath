import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

namespace Omega.Conclusion

open Submodule FiniteDimensional Module

/-- Affine representatives of a Serrin support class. -/
def serrinAffineRepresentative (x0 WK : ℝ × ℝ) (ρ : ℝ) : ℝ × ℝ :=
  x0 + ρ • WK

/-- Translation invariance removes the basepoint from the class representative. -/
def serrinTranslationNormalized (x0 WK : ℝ × ℝ) (ρ : ℝ) : ℝ × ℝ :=
  serrinAffineRepresentative x0 WK ρ - x0

/-- Positive `1`-homogeneity of the support-screen code. -/
def serrinSupportScreenCode (ΓWK : ℝ × ℝ) (ρ : ℝ) : ℝ × ℝ :=
  ρ • ΓWK

/-- The normalized-volume slice fixes the scale parameter to `ρ = 1`. -/
def serrinNormalizedSupportScreen (ΓWK : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {y | ∃ ρ : ℝ, ρ = 1 ∧ y = serrinSupportScreenCode ΓWK ρ}

/-- Paper label: `thm:conclusion-serrin-support-screen-rank-atmost-one`. Translation removes the
basepoint, positive `1`-homogeneity turns every class into a scalar multiple of a single screen
vector, and normalization fixes the scalar to `1`, so the normalized support screen spans at most
one dimension. -/
theorem paper_conclusion_serrin_support_screen_rank_atmost_one
    (x0 WK ΓWK : ℝ × ℝ) :
    (∀ ρ, serrinTranslationNormalized x0 WK ρ = ρ • WK) ∧
      (∀ ρ, serrinSupportScreenCode ΓWK ρ = ρ • ΓWK) ∧
      serrinNormalizedSupportScreen ΓWK = Set.range (fun _ : Unit => ΓWK) ∧
      Module.finrank ℝ (Submodule.span ℝ (serrinNormalizedSupportScreen ΓWK)) ≤ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ
    ext <;> simp [serrinTranslationNormalized, serrinAffineRepresentative]
  · intro ρ
    rfl
  · ext y
    constructor
    · rintro ⟨ρ, rfl, hy⟩
      refine ⟨(), ?_⟩
      simpa [serrinSupportScreenCode] using hy.symm
    · rintro ⟨_, rfl⟩
      exact ⟨1, rfl, by simp [serrinSupportScreenCode]⟩
  · have hset :
        serrinNormalizedSupportScreen ΓWK = Set.range (fun _ : Unit => ΓWK) := by
      ext y
      constructor
      · rintro ⟨ρ, rfl, hy⟩
        refine ⟨(), ?_⟩
        simpa [serrinSupportScreenCode] using hy.symm
      · rintro ⟨_, rfl⟩
        exact ⟨1, rfl, by simp [serrinSupportScreenCode]⟩
    rw [hset]
    have hfinite : Set.Finite (Set.range fun _ : Unit => ΓWK) := Set.finite_range _
    haveI : Fintype (Set.range fun _ : Unit => ΓWK) := hfinite.fintype
    calc
      Module.finrank ℝ (Submodule.span ℝ (Set.range fun _ : Unit => ΓWK))
        ≤ (Set.range fun _ : Unit => ΓWK).toFinset.card := finrank_span_le_card _
      _ = Fintype.card (Set.range fun _ : Unit => ΓWK) := by rw [Set.toFinset_card]
      _ ≤ Fintype.card Unit := Fintype.card_range_le (fun _ : Unit => ΓWK)
      _ = 1 := by simp

end Omega.Conclusion
