import Omega.Conclusion.FixedResolutionAxialScreenCorankAreaLaw
import Omega.Conclusion.FullInternalScreenGlobalComplementLaw
import Omega.Conclusion.ScreenKolmogorovDeficitExactSplitting

namespace Omega.Conclusion

/-- The hidden rank on the axial screen is the codimension-one area-law term. -/
def conclusion_axial_screen_direct_sum_visible_hidden_split_hidden_rank (m n : ℕ) : ℕ :=
  2 ^ (m * (n - 1))

/-- The visible block is the complement of one hidden slice in each of the `2^m` axial fibers. -/
def conclusion_axial_screen_direct_sum_visible_hidden_split_visible_dimension (m n : ℕ) : ℕ :=
  (2 ^ m - 1) *
    conclusion_axial_screen_direct_sum_visible_hidden_split_hidden_rank m n

/-- Hidden `𝔽₂`-space. -/
abbrev conclusion_axial_screen_direct_sum_visible_hidden_split_hidden_space (m n : ℕ) :=
  Fin (conclusion_axial_screen_direct_sum_visible_hidden_split_hidden_rank m n) → ZMod 2

/-- Visible `𝔽₂`-space. -/
abbrev conclusion_axial_screen_direct_sum_visible_hidden_split_visible_space (m n : ℕ) :=
  Fin (conclusion_axial_screen_direct_sum_visible_hidden_split_visible_dimension m n) → ZMod 2

/-- Total visible/hidden package as an explicit product. -/
abbrev conclusion_axial_screen_direct_sum_visible_hidden_split_total_space (m n : ℕ) :=
  conclusion_axial_screen_direct_sum_visible_hidden_split_hidden_space m n ×
    conclusion_axial_screen_direct_sum_visible_hidden_split_visible_space m n

/-- Concrete conclusion package for the axial-screen visible/hidden split: the hidden rank is the
axial audit cost, the full internal screen contributes the unique residual generator, projection to
the hidden block is surjective, the generic finite-dimensional exact-sequence splitting applies,
and the finite product has the expected cardinality. -/
def conclusion_axial_screen_direct_sum_visible_hidden_split_statement : Prop :=
  ∀ m n : ℕ,
    Omega.SPG.CoordinateBundleScreenCount.auditCost m n 1 =
        conclusion_axial_screen_direct_sum_visible_hidden_split_hidden_rank m n ∧
      fullInternalScreenKernelRank m n = 1 ∧
      Function.Surjective
        (fun x : conclusion_axial_screen_direct_sum_visible_hidden_split_total_space m n => x.1) ∧
      (∃ r : ℕ,
        ∃ _h :
          conclusion_axial_screen_direct_sum_visible_hidden_split_total_space m n →ₗ[ZMod 2]
            (Fin r → ZMod 2),
          Nonempty
            (conclusion_axial_screen_direct_sum_visible_hidden_split_total_space m n ≃ₗ[ZMod 2]
              (LinearMap.range
                  (LinearMap.fst
                    (R := ZMod 2)
                    (M := conclusion_axial_screen_direct_sum_visible_hidden_split_hidden_space m n)
                    (M₂ := conclusion_axial_screen_direct_sum_visible_hidden_split_visible_space
                      m n)) ×
                (Fin r → ZMod 2))) ∧
            Fintype.card
                (conclusion_axial_screen_direct_sum_visible_hidden_split_total_space m n) =
              2 ^ conclusion_axial_screen_direct_sum_visible_hidden_split_hidden_rank m n *
                2 ^ conclusion_axial_screen_direct_sum_visible_hidden_split_visible_dimension
                  m n)

/-- Paper label: `cor:conclusion-axial-screen-direct-sum-visible-hidden-split`. -/
theorem paper_conclusion_axial_screen_direct_sum_visible_hidden_split :
    conclusion_axial_screen_direct_sum_visible_hidden_split_statement := by
  intro m n
  refine ⟨paper_conclusion_fixedresolution_axial_screen_corank_area_law m n, ?_, ?_, ?_⟩
  · exact (paper_conclusion_full_internal_screen_global_complement_law m n).2.1
  · intro y
    exact ⟨(y, 0), rfl⟩
  · let f :
        conclusion_axial_screen_direct_sum_visible_hidden_split_total_space m n →ₗ[ZMod 2]
          conclusion_axial_screen_direct_sum_visible_hidden_split_hidden_space m n :=
      LinearMap.fst
        (R := ZMod 2)
        (M := conclusion_axial_screen_direct_sum_visible_hidden_split_hidden_space m n)
        (M₂ := conclusion_axial_screen_direct_sum_visible_hidden_split_visible_space m n)
    rcases paper_conclusion_screen_kolmogorov_deficit_exact_splitting f with ⟨r, h, hsplit⟩
    refine ⟨r, h, ?_, ?_⟩
    · simpa [f]
    · simp [conclusion_axial_screen_direct_sum_visible_hidden_split_total_space,
        conclusion_axial_screen_direct_sum_visible_hidden_split_hidden_space,
        conclusion_axial_screen_direct_sum_visible_hidden_split_visible_space,
        conclusion_axial_screen_direct_sum_visible_hidden_split_hidden_rank,
        conclusion_axial_screen_direct_sum_visible_hidden_split_visible_dimension]

end Omega.Conclusion
