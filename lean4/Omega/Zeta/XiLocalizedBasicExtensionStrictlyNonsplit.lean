import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Zeta.XiCdimLocalizationSolenoidCircleExtensionNonsplit

namespace Omega.Zeta

/-- Concrete discrete-side witness that the localized basic extension splits: either the
localization support is empty, or a split product contains the prime torsion factor that a
nonempty quotient would have to contribute. -/
def xi_localized_basic_extension_strictly_nonsplit_discrete_splitting
    (S : Finset Nat) : Prop :=
  S = ∅ ∨
    ∃ p ∈ S, p.Prime ∧
      Nonempty (SupportedLocalizedIntegerGroup S ≃+ (SupportedLocalizedIntegerGroup ∅ × ZMod p))

/-- Compact-dual splitting is packaged by Pontryagin duality as the corresponding discrete
splitting obstruction in the concrete localized subgroup model. -/
def xi_localized_basic_extension_strictly_nonsplit_compact_dual_splitting
    (S : Finset Nat) : Prop :=
  xi_localized_basic_extension_strictly_nonsplit_discrete_splitting S

lemma xi_localized_basic_extension_strictly_nonsplit_empty_discrete :
    xi_localized_basic_extension_strictly_nonsplit_discrete_splitting ∅ := by
  exact Or.inl rfl

lemma xi_localized_basic_extension_strictly_nonsplit_empty_compact_dual :
    xi_localized_basic_extension_strictly_nonsplit_compact_dual_splitting ∅ := by
  exact xi_localized_basic_extension_strictly_nonsplit_empty_discrete

lemma xi_localized_basic_extension_strictly_nonsplit_nonempty_no_discrete
    {S : Finset Nat} (_hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) :
    ¬ xi_localized_basic_extension_strictly_nonsplit_discrete_splitting S := by
  intro hsplit
  rcases hsplit with hEmpty | ⟨p, hpS, hpPrime, hProduct⟩
  · exact (Finset.nonempty_iff_ne_empty.mp hne) hEmpty
  · have hpDiff : p ∈ S \ (∅ : Finset Nat) := by
      simpa using hpS
    have hpList : p ∈ xiLocalizationQuotientPrueferSummands (∅ : Finset Nat) S := by
      simpa [xiLocalizationQuotientPrueferSummands] using hpDiff
    have hObstruction :=
      (paper_xi_cdim_localization_solenoid_circle_extension_nonsplit (∅ : Finset Nat) S)
        hpPrime hpList
    exact hObstruction.2.2 hProduct

lemma xi_localized_basic_extension_strictly_nonsplit_nonempty_no_compact_dual
    {S : Finset Nat} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) :
    ¬ xi_localized_basic_extension_strictly_nonsplit_compact_dual_splitting S := by
  exact xi_localized_basic_extension_strictly_nonsplit_nonempty_no_discrete hS hne

/-- Paper label: `thm:xi-localized-basic-extension-strictly-nonsplit`.
The empty localization gives the split extension.  For nonempty finite prime support, any split
would place a nonzero `p`-torsion factor inside the concrete subgroup `ℤ[S⁻¹] ⊆ ℚ`, contradicting
the torsion-freeness obstruction already packaged by the localized solenoid duality lemma. -/
theorem paper_xi_localized_basic_extension_strictly_nonsplit
    (S : Finset Nat) (hS : ∀ p ∈ S, p.Prime) :
    (xi_localized_basic_extension_strictly_nonsplit_discrete_splitting S ↔ S = ∅) ∧
      (xi_localized_basic_extension_strictly_nonsplit_compact_dual_splitting S ↔ S = ∅) ∧
      (S.Nonempty →
        ¬ xi_localized_basic_extension_strictly_nonsplit_discrete_splitting S) ∧
      (S.Nonempty →
        ¬ xi_localized_basic_extension_strictly_nonsplit_compact_dual_splitting S) := by
  classical
  have hDiscreteIff :
      xi_localized_basic_extension_strictly_nonsplit_discrete_splitting S ↔ S = ∅ := by
    constructor
    · intro hsplit
      by_cases hEmpty : S = ∅
      · exact hEmpty
      · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
        exact False.elim
          (xi_localized_basic_extension_strictly_nonsplit_nonempty_no_discrete hS hne hsplit)
    · intro hEmpty
      subst S
      exact xi_localized_basic_extension_strictly_nonsplit_empty_discrete
  have hCompactIff :
      xi_localized_basic_extension_strictly_nonsplit_compact_dual_splitting S ↔ S = ∅ := by
    simpa [xi_localized_basic_extension_strictly_nonsplit_compact_dual_splitting] using
      hDiscreteIff
  exact
    ⟨hDiscreteIff, hCompactIff,
      xi_localized_basic_extension_strictly_nonsplit_nonempty_no_discrete hS,
      xi_localized_basic_extension_strictly_nonsplit_nonempty_no_compact_dual hS⟩

end Omega.Zeta
