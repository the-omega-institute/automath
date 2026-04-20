import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersConnectedRationalBlindness

namespace Omega.Zeta

/-- A rational has `S`-supported denominator if every prime dividing its denominator lies in `S`. -/
def denominatorSupportedBy (S : Finset Nat) (q : ℚ) : Prop :=
  ∀ p : Nat, p.Prime → p ∣ q.den → p ∈ S

lemma denominatorSupportedBy_zero (S : Finset Nat) : denominatorSupportedBy S 0 := by
  intro p hp hdiv
  have hdiv' : p ∣ 1 := by simpa using hdiv
  exact False.elim (hp.not_dvd_one hdiv')

lemma denominatorSupportedBy_intCast (S : Finset Nat) (n : ℤ) : denominatorSupportedBy S n := by
  intro p hp hdiv
  have hdiv' : p ∣ 1 := by simpa using hdiv
  exact False.elim (hp.not_dvd_one hdiv')

lemma denominatorSupportedBy_neg {S : Finset Nat} {q : ℚ} (hq : denominatorSupportedBy S q) :
    denominatorSupportedBy S (-q) := by
  intro p hp hdiv
  exact hq p hp (by simpa [Rat.den_neg_eq_den] using hdiv)

lemma denominatorSupportedBy_add {S : Finset Nat} {q r : ℚ}
    (hq : denominatorSupportedBy S q) (hr : denominatorSupportedBy S r) :
    denominatorSupportedBy S (q + r) := by
  intro p hp hdiv
  have hprod : p ∣ q.den * r.den := dvd_trans hdiv (Rat.add_den_dvd q r)
  rcases hp.dvd_mul.mp hprod with hqden | hrden
  · exact hq p hp hqden
  · exact hr p hp hrden

lemma denominatorSupportedBy_mul {S : Finset Nat} {q r : ℚ}
    (hq : denominatorSupportedBy S q) (hr : denominatorSupportedBy S r) :
    denominatorSupportedBy S (q * r) := by
  intro p hp hdiv
  have hprod : p ∣ q.den * r.den := dvd_trans hdiv (Rat.mul_den_dvd q r)
  rcases hp.dvd_mul.mp hprod with hqden | hrden
  · exact hq p hp hqden
  · exact hr p hp hrden

/-- The additive subgroup `ℤ[S⁻¹]` realized inside `ℚ` by the denominator-support condition. -/
def localizedIntegerSubgroup (S : Finset Nat) : AddSubgroup ℚ where
  carrier := {q : ℚ | denominatorSupportedBy S q}
  zero_mem' := denominatorSupportedBy_zero S
  add_mem' := fun hq hr => denominatorSupportedBy_add hq hr
  neg_mem' := fun hq => denominatorSupportedBy_neg hq

/-- The local additive group `G_S = ℤ[S⁻¹]` used in this file. -/
abbrev SupportedLocalizedIntegerGroup (S : Finset Nat) := ↥(localizedIntegerSubgroup S)

/-- The element `1` in the localized integer group. -/
def localizedOne (S : Finset Nat) : SupportedLocalizedIntegerGroup S :=
  ⟨1, denominatorSupportedBy_intCast S 1⟩

/-- Scalar multiplication by a localized rational defines an additive endomorphism. -/
def localizedScalarEndomorphism {S : Finset Nat} (u : SupportedLocalizedIntegerGroup S) :
    SupportedLocalizedIntegerGroup S →+ SupportedLocalizedIntegerGroup S where
  toFun x := ⟨u.1 * x.1, denominatorSupportedBy_mul u.2 x.2⟩
  map_zero' := by
    ext
    simp
  map_add' x y := by
    ext
    simp [mul_add]

/-- Scalar multiplication by a supported unit of the localization defines an additive
automorphism. -/
def localizedScalarAutomorphism {S : Finset Nat} (u : SupportedLocalizedIntegerGroup S)
    (hu0 : u.1 ≠ 0) (huinv : denominatorSupportedBy S u.1⁻¹) :
    SupportedLocalizedIntegerGroup S ≃+ SupportedLocalizedIntegerGroup S where
  toFun x := ⟨u.1 * x.1, denominatorSupportedBy_mul u.2 x.2⟩
  invFun x := ⟨u.1⁻¹ * x.1, denominatorSupportedBy_mul huinv x.2⟩
  left_inv x := by
    ext
    simp [hu0]
  right_inv x := by
    ext
    simp [hu0]
  map_add' x y := by
    ext
    simp [mul_add]

/-- Concrete explicit package for localized integers: supported scalars act by endomorphisms, and
supported units act by automorphisms. -/
def LocalizedIntegersEndomorphismAutomorphismExplicit (S : Finset Nat) : Prop :=
  (∀ u : SupportedLocalizedIntegerGroup S,
      ∃ φ : SupportedLocalizedIntegerGroup S →+ SupportedLocalizedIntegerGroup S,
        ∀ x : SupportedLocalizedIntegerGroup S, (φ x : ℚ) = u.1 * x.1) ∧
    (∀ u : SupportedLocalizedIntegerGroup S,
      u.1 ≠ 0 →
      denominatorSupportedBy S u.1⁻¹ →
      ∃ σ : SupportedLocalizedIntegerGroup S ≃+ SupportedLocalizedIntegerGroup S,
        ∀ x : SupportedLocalizedIntegerGroup S, (σ x : ℚ) = u.1 * x.1)

/-- In the concrete subgroup model `G_S = ℤ[S⁻¹] ⊆ ℚ`, every supported scalar gives an additive
endomorphism and every supported unit gives an additive automorphism.
    thm:xi-localized-integers-endomorphism-automorphism-explicit -/
theorem paper_xi_localized_integers_endomorphism_automorphism_explicit (S : Finset Nat) :
    LocalizedIntegersEndomorphismAutomorphismExplicit S := by
  refine ⟨?_, ?_⟩
  · intro u
    refine ⟨localizedScalarEndomorphism u, ?_⟩
    intro x
    rfl
  · intro u hu0 huinv
    refine ⟨localizedScalarAutomorphism u hu0 huinv, ?_⟩
    intro x
    rfl

end Omega.Zeta
