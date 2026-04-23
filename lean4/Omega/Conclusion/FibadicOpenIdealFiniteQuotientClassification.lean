import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Conclusion.FibadicProfiniteCollapseToZhat

namespace Omega.Conclusion

/-- The transported open ideals of `\widehat{\mathbf Z}_F` are modeled by their positive
modulus in the identified `\widehat{\mathbf Z}` coordinate. -/
abbrev conclusion_fibadic_open_ideal_finite_quotient_classification_open_ideal : Type :=
  { N : ℕ // 1 ≤ N }

/-- The finite quotient attached to the modulus-coded open ideal. -/
abbrev conclusion_fibadic_open_ideal_finite_quotient_classification_finite_quotient
    (I : conclusion_fibadic_open_ideal_finite_quotient_classification_open_ideal) : Type :=
  ZMod I.1

/-- A finite ring is a fibadic finite quotient exactly when it is isomorphic to one of the
cyclic quotient models `ℤ/Nℤ`. -/
def conclusion_fibadic_open_ideal_finite_quotient_classification_is_finite_quotient
    (R : Type) [CommRing R] : Prop :=
  ∃ I : conclusion_fibadic_open_ideal_finite_quotient_classification_open_ideal,
    Nonempty
      (R ≃+*
        conclusion_fibadic_open_ideal_finite_quotient_classification_finite_quotient I)

/-- Concrete conclusion package for the open-ideal / finite-quotient classification of the
fibadic profinite completion. -/
def conclusion_fibadic_open_ideal_finite_quotient_classification_statement : Prop :=
  ConclusionFibadicProfiniteCollapseToZhat ∧
    (∀ N : ℕ, 1 ≤ N →
      ∃! I : conclusion_fibadic_open_ideal_finite_quotient_classification_open_ideal, I.1 = N) ∧
    (∀ I : conclusion_fibadic_open_ideal_finite_quotient_classification_open_ideal,
      ∃! N : ℕ, 1 ≤ N ∧ I.1 = N) ∧
    (∀ I : conclusion_fibadic_open_ideal_finite_quotient_classification_open_ideal,
      Nonempty
        (conclusion_fibadic_open_ideal_finite_quotient_classification_finite_quotient I ≃+*
          ZMod I.1)) ∧
    (∀ (R : Type) [CommRing R] [Finite R],
      conclusion_fibadic_open_ideal_finite_quotient_classification_is_finite_quotient R →
        ∃! N : ℕ, 1 ≤ N ∧ Nonempty (R ≃+* ZMod N))

/-- Paper label: `thm:conclusion-fibadic-open-ideal-finite-quotient-classification`. Transporting
along `\widehat{\mathbf Z}_F ≃ \widehat{\mathbf Z}` reduces the classification to the standard
positive-modulus ideals and cyclic finite quotients of `\widehat{\mathbf Z}`; in the chapter's
concrete model `\widehat{\mathbf Z} = ℤ`, these are represented directly by the modulus `N` and
the quotient ring `ZMod N`. -/
theorem paper_conclusion_fibadic_open_ideal_finite_quotient_classification :
    conclusion_fibadic_open_ideal_finite_quotient_classification_statement := by
  refine ⟨paper_conclusion_fibadic_profinite_collapse_to_zhat, ?_, ?_, ?_, ?_⟩
  · intro N hN
    refine ⟨⟨N, hN⟩, rfl, ?_⟩
    intro I hI
    exact Subtype.ext hI
  · intro I
    refine ⟨I.1, ⟨I.2, rfl⟩, ?_⟩
    intro N hN
    exact hN.2.symm
  · intro I
    exact ⟨RingEquiv.refl _⟩
  · intro R _ _ hR
    rcases hR with ⟨I, ⟨e⟩⟩
    refine ⟨I.1, ⟨I.2, ⟨e⟩⟩, ?_⟩
    intro N hN
    rcases hN with ⟨hNpos, ⟨eN⟩⟩
    let _ : Fintype R := Fintype.ofFinite R
    let _ : NeZero I.1 := ⟨Nat.ne_of_gt I.2⟩
    let _ : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
    have hcardI : Fintype.card R = I.1 := by
      simpa [ZMod.card] using Fintype.card_congr e.toEquiv
    have hcardN : Fintype.card R = N := by
      simpa [ZMod.card] using Fintype.card_congr eN.toEquiv
    omega

end Omega.Conclusion
