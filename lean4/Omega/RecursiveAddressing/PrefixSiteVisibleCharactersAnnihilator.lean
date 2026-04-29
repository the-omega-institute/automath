import Omega.RecursiveAddressing.PrefixSiteMinVisibleQuotient

namespace Omega.RecursiveAddressing

theorem paper_recursive_addressing_prefix_site_visible_characters_annihilator
    {ι A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (α : ι → A) (χ : A →+ B) :
    (∀ i, χ (α i) = 0) ↔ PointwiseInvisible.cocycleValueSubgroup α ≤ χ.ker := by
  constructor
  · intro hχ
    exact PointwiseInvisible.cocycleValueSubgroup_le_ker α χ hχ
  · intro hker i
    have hmem : α i ∈ PointwiseInvisible.cocycleValueSubgroup α :=
      AddSubgroup.subset_closure ⟨i, rfl⟩
    have hzero : α i ∈ χ.ker := hker hmem
    simpa [AddMonoidHom.mem_ker] using hzero

/-- Paper label: `cor:prefix-site-visible-characters-annihilator`. -/
theorem paper_prefix_site_visible_characters_annihilator
    {ι A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (α : ι → A) (χ : A →+ B) :
    (∀ i, χ (α i) = 0) ↔ PointwiseInvisible.cocycleValueSubgroup α ≤ χ.ker :=
  paper_recursive_addressing_prefix_site_visible_characters_annihilator α χ

end Omega.RecursiveAddressing
