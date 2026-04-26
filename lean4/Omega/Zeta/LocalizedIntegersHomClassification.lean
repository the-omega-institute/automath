import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersEndomorphismAutomorphismExplicit

namespace Omega.Zeta

/-- Denominator support is monotone in the finite prime set. -/
lemma xi_localized_integers_hom_classification_denominatorSupportedBy_mono
    {S T : Finset Nat} (hST : S ⊆ T) {q : ℚ}
    (hq : denominatorSupportedBy S q) :
    denominatorSupportedBy T q := by
  intro p hp hdiv
  exact hST (hq p hp hdiv)

/-- Scalar multiplication by an element of `G_T` maps `G_S` into `G_T` whenever `S ⊆ T`. -/
def xi_localized_integers_hom_classification_scalarHom {S T : Finset Nat}
    (hST : S ⊆ T) (u : SupportedLocalizedIntegerGroup T) :
    SupportedLocalizedIntegerGroup S →+ SupportedLocalizedIntegerGroup T where
  toFun x :=
    ⟨u.1 * x.1,
      denominatorSupportedBy_mul u.2
        (xi_localized_integers_hom_classification_denominatorSupportedBy_mono hST x.2)⟩
  map_zero' := by
    ext
    simp
  map_add' x y := by
    ext
    simp [mul_add]

/-- Concrete hom-classification statement for the supported-denominator model.  In the comparable
case `S ⊆ T`, supported scalars in `G_T` give the unique scalar homomorphism with prescribed value
on `1`; in the non-comparable case the finite sets expose a missing denominator direction. -/
def xi_localized_integers_hom_classification_statement (S T : Finset Nat) : Prop :=
  (S ⊆ T →
    ∀ u : SupportedLocalizedIntegerGroup T,
      ∃! φ : SupportedLocalizedIntegerGroup S →+ SupportedLocalizedIntegerGroup T,
        φ (localizedOne S) = u ∧
          ∀ x : SupportedLocalizedIntegerGroup S, (φ x : ℚ) = u.1 * x.1) ∧
    (¬ S ⊆ T → ∃ p : Nat, p ∈ S ∧ p ∉ T)

/-- Paper label: `thm:xi-localized-integers-hom-classification`. -/
theorem paper_xi_localized_integers_hom_classification (S T : Finset Nat) :
    xi_localized_integers_hom_classification_statement S T := by
  constructor
  · intro hST u
    refine
      ⟨xi_localized_integers_hom_classification_scalarHom hST u, ?_, ?_⟩
    · constructor
      · ext
        simp [xi_localized_integers_hom_classification_scalarHom, localizedOne]
      · intro x
        rfl
    · intro ψ hψ
      ext x
      change (ψ x : ℚ) = u.1 * x.1
      exact hψ.2 x
  · intro hnot
    rw [Finset.not_subset] at hnot
    exact hnot

end Omega.Zeta
