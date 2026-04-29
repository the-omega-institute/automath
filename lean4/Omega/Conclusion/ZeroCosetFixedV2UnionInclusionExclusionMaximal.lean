import Omega.Conclusion.ZeroCosetFixedV2FiniteIntersectionGcd

namespace Omega.Conclusion

/-- Finite union of the concrete zero-cosets `S_g(M)` over a list of divisors. -/
def conclusion_zero_coset_fixed_v2_union_inclusion_exclusion_maximal_union
    (M : ℕ) : List ℕ → Finset ℕ
  | [] => ∅
  | g :: gs =>
      Omega.Folding.sgMFrequencySet M g ∪
        conclusion_zero_coset_fixed_v2_union_inclusion_exclusion_maximal_union M gs

/-- In the unit same-`v₂` layer, the maximal representative is the gcd representative. -/
def conclusion_zero_coset_fixed_v2_union_inclusion_exclusion_maximal_family
    (gs : List ℕ) : List ℕ :=
  [listGcd gs]

/-- Concrete unit-layer form of the maximal-family union equality and its cardinality. -/
def conclusion_zero_coset_fixed_v2_union_inclusion_exclusion_maximal_statement : Prop :=
  ∀ M : ℕ, ∀ gs : List ℕ,
    0 < M →
      gs != [] →
        Even M →
          (∀ g ∈ gs, g ∣ M / 2) →
            sameV2Layer gs →
              conclusion_zero_coset_fixed_v2_union_inclusion_exclusion_maximal_union M gs =
                  conclusion_zero_coset_fixed_v2_union_inclusion_exclusion_maximal_union M
                    (conclusion_zero_coset_fixed_v2_union_inclusion_exclusion_maximal_family gs) ∧
                (conclusion_zero_coset_fixed_v2_union_inclusion_exclusion_maximal_union M gs).card =
                  listGcd gs

/-- Paper label: `cor:conclusion-zero-coset-fixed-v2-union-inclusion-exclusion-maximal`. -/
theorem paper_conclusion_zero_coset_fixed_v2_union_inclusion_exclusion_maximal :
    conclusion_zero_coset_fixed_v2_union_inclusion_exclusion_maximal_statement := by
  intro M gs hM hgs hEven hdiv hsame
  have _hintersection :=
    paper_conclusion_zero_coset_fixed_v2_finite_intersection_gcd M gs hgs hEven hdiv hsame
  have hgcd : listGcd gs = 1 := by
    have hgcd_aux : ∀ xs : List ℕ, xs != [] → sameV2Layer xs → listGcd xs = 1 := by
      intro xs hxs hsame_xs
      induction xs with
      | nil =>
          simp at hxs
      | cons g tail ih =>
          have hg : g = 1 := hsame_xs g (by simp)
          subst hg
          by_cases htail : tail = []
          · subst htail
            simp [listGcd]
          · have htail_ne : tail != [] := by simpa using htail
            have hsame_tail : sameV2Layer tail := by
              intro x hx
              exact hsame_xs x (by simp [hx])
            rw [listGcd, ih htail_ne hsame_tail, Nat.gcd_self]
    exact hgcd_aux gs hgs hsame
  have hunion :
      conclusion_zero_coset_fixed_v2_union_inclusion_exclusion_maximal_union M gs =
        Omega.Folding.sgMFrequencySet M 1 := by
    have hunion_aux : ∀ xs : List ℕ,
        xs != [] →
          sameV2Layer xs →
            conclusion_zero_coset_fixed_v2_union_inclusion_exclusion_maximal_union M xs =
              Omega.Folding.sgMFrequencySet M 1 := by
      intro xs hxs hsame_xs
      induction xs with
      | nil =>
          simp at hxs
      | cons g tail ih =>
          have hg : g = 1 := hsame_xs g (by simp)
          subst hg
          by_cases htail : tail = []
          · subst htail
            simp [conclusion_zero_coset_fixed_v2_union_inclusion_exclusion_maximal_union]
          · have htail_ne : tail != [] := by simpa using htail
            have hsame_tail : sameV2Layer tail := by
              intro x hx
              exact hsame_xs x (by simp [hx])
            rw [conclusion_zero_coset_fixed_v2_union_inclusion_exclusion_maximal_union,
              ih htail_ne hsame_tail]
            simp
    exact hunion_aux gs hgs hsame
  constructor
  · rw [hunion, conclusion_zero_coset_fixed_v2_union_inclusion_exclusion_maximal_family, hgcd]
    simp [conclusion_zero_coset_fixed_v2_union_inclusion_exclusion_maximal_union]
  · rw [hunion, hgcd]
    simpa using Omega.Folding.sgMFrequencySet_card M 1 hM

end Omega.Conclusion
