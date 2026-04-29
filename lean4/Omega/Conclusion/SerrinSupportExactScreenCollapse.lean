import Mathlib.Data.Set.Image
import Mathlib.Tactic
import Omega.Conclusion.SerrinSupportScreenRankAtmostOne

namespace Omega.Conclusion

/-- The Serrin support screen image is the ray spanned by `Γ_m(W_K)`. -/
def conclusion_serrin_support_exact_screen_collapse_support
    (ΓWK : ℝ × ℝ) : Set (ℝ × ℝ) :=
  Set.range (serrinSupportScreenCode ΓWK)

/-- An exact one-dimensional screen on `S` is a linear functional that is injective on `S`. -/
def conclusion_serrin_support_exact_screen_collapse_exact_screen
    (S : Set (ℝ × ℝ)) : Prop :=
  ∃ ℓ : (ℝ × ℝ) →ₗ[ℝ] ℝ, Set.InjOn ℓ S

/-- Zero exact screen cost means that the visible class has already collapsed to a singleton. -/
def conclusion_serrin_support_exact_screen_collapse_zero_cost
    (S : Set (ℝ × ℝ)) : Prop :=
  S.Subsingleton

/-- The paper-facing exact-screen collapse statement for the Serrin support class. -/
def conclusion_serrin_support_exact_screen_collapse_statement
    (ΓWK : ℝ × ℝ) : Prop :=
  conclusion_serrin_support_exact_screen_collapse_exact_screen
      (conclusion_serrin_support_exact_screen_collapse_support ΓWK) ∧
    conclusion_serrin_support_exact_screen_collapse_zero_cost (serrinNormalizedSupportScreen ΓWK)

/-- A linear functional normalized by `ℓ(Γ_m(W_K)) = 1`. When the first coordinate vanishes, the
second one is nonzero because `Γ_m(W_K) ≠ 0`. -/
noncomputable def conclusion_serrin_support_exact_screen_collapse_normalized_functional
    (ΓWK : ℝ × ℝ) (_hΓ : ΓWK ≠ 0) : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  if hfst : ΓWK.1 ≠ 0 then
    (ΓWK.1)⁻¹ • LinearMap.fst ℝ ℝ ℝ
  else
    (ΓWK.2)⁻¹ • LinearMap.snd ℝ ℝ ℝ

lemma conclusion_serrin_support_exact_screen_collapse_normalized_functional_apply_generator
    (ΓWK : ℝ × ℝ) (hΓ : ΓWK ≠ 0) :
    conclusion_serrin_support_exact_screen_collapse_normalized_functional ΓWK hΓ ΓWK = 1 := by
  by_cases hfst : ΓWK.1 ≠ 0
  · simp [conclusion_serrin_support_exact_screen_collapse_normalized_functional, hfst]
  · have hsnd : ΓWK.2 ≠ 0 := by
      intro hsnd
      apply hΓ
      ext <;> simp [not_ne_iff.mp hfst, hsnd]
    simp [conclusion_serrin_support_exact_screen_collapse_normalized_functional, hfst, hsnd]

lemma conclusion_serrin_support_exact_screen_collapse_normalized_functional_recovers_scale
    (ΓWK : ℝ × ℝ) (hΓ : ΓWK ≠ 0) (ρ : ℝ) :
    conclusion_serrin_support_exact_screen_collapse_normalized_functional ΓWK hΓ
        (serrinSupportScreenCode ΓWK ρ) = ρ := by
  rw [serrinSupportScreenCode]
  calc
    conclusion_serrin_support_exact_screen_collapse_normalized_functional ΓWK hΓ (ρ • ΓWK)
        = ρ *
            conclusion_serrin_support_exact_screen_collapse_normalized_functional ΓWK hΓ ΓWK := by
              simp
    _ = ρ := by
      rw [conclusion_serrin_support_exact_screen_collapse_normalized_functional_apply_generator ΓWK hΓ]
      ring

/-- Paper label: `cor:conclusion-serrin-support-exact-screen-collapse`. The existing rank-at-most-
one support theorem turns the Serrin support image into a ray; if the generating vector is
nonzero, a normalized linear functional recovers the scale parameter on that ray, while the
volume-normalized class is a singleton and therefore has zero exact screen cost. -/
theorem paper_conclusion_serrin_support_exact_screen_collapse
    (x0 WK ΓWK : ℝ × ℝ) :
    conclusion_serrin_support_exact_screen_collapse_statement ΓWK := by
  rcases paper_conclusion_serrin_support_screen_rank_atmost_one x0 WK ΓWK with
    ⟨_htranslation, _hcode, hnormalized, _hrank⟩
  refine ⟨?_, ?_⟩
  · by_cases hΓ : ΓWK = 0
    · refine ⟨LinearMap.fst ℝ ℝ ℝ, ?_⟩
      intro y hy z hz _
      have hy0 : y = 0 := by
        rcases hy with ⟨ρ, rfl⟩
        simp [serrinSupportScreenCode, hΓ]
      have hz0 : z = 0 := by
        rcases hz with ⟨ρ, rfl⟩
        simp [serrinSupportScreenCode, hΓ]
      simpa [hy0, hz0]
    · refine
        ⟨conclusion_serrin_support_exact_screen_collapse_normalized_functional ΓWK hΓ, ?_⟩
      intro y hy z hz hEq
      rcases hy with ⟨ρy, rfl⟩
      rcases hz with ⟨ρz, rfl⟩
      have hρ : ρy = ρz := by
        simpa [conclusion_serrin_support_exact_screen_collapse_normalized_functional_recovers_scale,
          hΓ] using hEq
      simpa [serrinSupportScreenCode, hρ]
  · rw [hnormalized]
    simpa [conclusion_serrin_support_exact_screen_collapse_zero_cost] using
      (Set.subsingleton_range (fun _ : Unit => ΓWK))

end Omega.Conclusion
