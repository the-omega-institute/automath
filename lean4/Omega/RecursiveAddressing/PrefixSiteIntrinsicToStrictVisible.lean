import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

namespace Omega.RecursiveAddressing

/-- If the intrinsic hidden subgroup is contained in the strict hidden subgroup, the quotient by
the intrinsic subgroup maps naturally and surjectively onto the strict visible quotient.
    cor:prefix-site-intrinsic-to-strict-visible -/
theorem paper_prefix_site_intrinsic_to_strict_visible
    {A : Type*} [AddCommGroup A] (K H : AddSubgroup A) (hKH : K ≤ H) :
    ∃ q : A ⧸ K →+ A ⧸ H, Function.Surjective q := by
  let q : A ⧸ K →+ A ⧸ H :=
    QuotientAddGroup.lift K (QuotientAddGroup.mk' H) (by
      intro a ha
      exact (QuotientAddGroup.eq_zero_iff a).2 (hKH ha))
  refine ⟨q, ?_⟩
  intro y
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective H y
  exact ⟨QuotientAddGroup.mk' K a, by simp [q]⟩

end Omega.RecursiveAddressing
