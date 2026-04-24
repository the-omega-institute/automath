import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersEndomorphismAutomorphismExplicit

namespace Omega.Zeta

open scoped BigOperators

/-- The prime coordinates of a finite localization set. -/
abbrev LocalizedPrimeCoordinate (S : FinitePrimeLocalization) := ↥(S.attach.filter fun p => Nat.Prime p.1)

/-- A localized unit is described by a sign together with an integer exponent on each prime
coordinate. This is the concrete `C₂ × ℤ^r` coordinate model used in the file. -/
abbrev LocalizedUnitCoordinates (S : FinitePrimeLocalization) :=
  Bool × (LocalizedPrimeCoordinate S → ℤ)

/-- One prime-power factor appearing in the unit coordinates. Positive exponents stay in `ℤ`,
negative exponents contribute inverse prime powers. -/
def localizedSignedPrimePower (p : ℕ) (n : ℤ) : ℚ :=
  if 0 ≤ n then ((p ^ Int.toNat n : ℕ) : ℚ) else (((p ^ Int.toNat (-n) : ℕ) : ℚ)⁻¹)

/-- The scalar in `ℚ` encoded by a localized unit coordinate. -/
noncomputable def localizedUnitScalar (S : FinitePrimeLocalization) (u : LocalizedUnitCoordinates S) :
    ℚ :=
  (if u.1 then (-1 : ℚ) else 1) *
    ∏ p : LocalizedPrimeCoordinate S, localizedSignedPrimePower p.1.1 (u.2 p)

/-- Negating the exponent vector gives the inverse unit coordinates. -/
def localizedUnitCoordinatesInv {S : FinitePrimeLocalization} (u : LocalizedUnitCoordinates S) :
    LocalizedUnitCoordinates S :=
  (u.1, fun p => -u.2 p)

/-- Paper-facing classification package for localized unit automorphisms. The first component says
that every explicit `C₂ × ℤ^r` unit coordinate gives a supported nonzero scalar with supported
inverse, hence an additive automorphism of `ℤ[S⁻¹] ⊆ ℚ`. The second component records the explicit
coordinate identification with `C₂ × ℤ^r`. -/
def LocalizedUnitAutomorphismGroupClassification (S : Omega.Zeta.FinitePrimeLocalization) : Prop :=
  (∀ u : LocalizedUnitCoordinates S,
      denominatorSupportedBy S (localizedUnitScalar S u) ∧
        localizedUnitScalar S u ≠ 0 ∧
        denominatorSupportedBy S (localizedUnitScalar S u)⁻¹ ∧
          ∃ σ : SupportedLocalizedIntegerGroup S ≃+ SupportedLocalizedIntegerGroup S,
            ∀ x : SupportedLocalizedIntegerGroup S, (σ x : ℚ) = localizedUnitScalar S u * x.1) ∧
    Nonempty (LocalizedUnitCoordinates S ≃ Bool × (LocalizedPrimeCoordinate S → ℤ))

private lemma localizedPrimeCoordinate_mem {S : FinitePrimeLocalization} (p : LocalizedPrimeCoordinate S) :
    p.1.1 ∈ S := by
  have hp : p.1 ∈ S.attach.filter fun q => Nat.Prime q.1 := p.2
  simpa using (Finset.mem_filter.mp hp).1

private lemma localizedPrimeCoordinate_prime {S : FinitePrimeLocalization}
    (p : LocalizedPrimeCoordinate S) : p.1.1.Prime := by
  have hp : p.1 ∈ S.attach.filter fun q => Nat.Prime q.1 := p.2
  simpa using (Finset.mem_filter.mp hp).2

private lemma denominatorSupportedBy_inv_primePow (S : Finset Nat) {p : ℕ} (hp : p.Prime)
    (hpS : p ∈ S) (n : ℕ) : denominatorSupportedBy S (((p ^ n : ℕ) : ℚ)⁻¹) := by
  intro q hq hqden
  rw [Rat.inv_natCast_den_of_pos (pow_pos hp.pos n)] at hqden
  have hqp_dvd : q ∣ p := hq.dvd_of_dvd_pow hqden
  rcases (Nat.dvd_prime hp).mp hqp_dvd with hq1 | hqp
  · exact False.elim (hq.ne_one hq1)
  · simpa [hqp] using hpS

private lemma denominatorSupportedBy_prod (S : Finset Nat) {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℚ) (hf : ∀ a ∈ s, denominatorSupportedBy S (f a)) :
    denominatorSupportedBy S (s.prod f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using denominatorSupportedBy_intCast S 1
  | @insert a s ha ih =>
      have ha' : denominatorSupportedBy S (f a) := hf a (by simp [ha])
      have hs' : denominatorSupportedBy S (s.prod f) := ih (by
        intro b hb
        exact hf b (by simp [hb]))
      simpa [Finset.prod_insert, ha] using denominatorSupportedBy_mul ha' hs'

private lemma denominatorSupportedBy_sign (S : Finset Nat) (ε : Bool) :
    denominatorSupportedBy S (if ε then (-1 : ℚ) else 1) := by
  cases ε
  · simpa using denominatorSupportedBy_intCast S 1
  · simpa using denominatorSupportedBy_intCast S (-1)

private lemma denominatorSupportedBy_localizedSignedPrimePower {S : Finset Nat} {p : ℕ}
    (hpS : p ∈ S) (hp : p.Prime) (n : ℤ) :
    denominatorSupportedBy S (localizedSignedPrimePower p n) := by
  by_cases h : 0 ≤ n
  · simpa [localizedSignedPrimePower, h] using
      denominatorSupportedBy_intCast S ((p ^ Int.toNat n : ℕ) : ℤ)
  · simpa [localizedSignedPrimePower, h] using
      denominatorSupportedBy_inv_primePow S hp hpS (Int.toNat (-n))

private lemma localizedSignedPrimePower_nonzero {p : ℕ} (hp : p.Prime) (n : ℤ) :
    localizedSignedPrimePower p n ≠ 0 := by
  by_cases h : 0 ≤ n
  · simp [localizedSignedPrimePower, h, hp.ne_zero]
  · simp [localizedSignedPrimePower, h, hp.ne_zero]

private lemma denominatorSupportedBy_localizedUnitScalar (S : FinitePrimeLocalization)
    (u : LocalizedUnitCoordinates S) : denominatorSupportedBy S (localizedUnitScalar S u) := by
  classical
  unfold localizedUnitScalar
  apply denominatorSupportedBy_mul
  · exact denominatorSupportedBy_sign S u.1
  · exact denominatorSupportedBy_prod S Finset.univ
      (fun p : LocalizedPrimeCoordinate S => localizedSignedPrimePower p.1.1 (u.2 p)) (by
        intro p hp
        exact denominatorSupportedBy_localizedSignedPrimePower
          (localizedPrimeCoordinate_mem p) (localizedPrimeCoordinate_prime p) (u.2 p))

private lemma localizedUnitScalar_nonzero (S : FinitePrimeLocalization) (u : LocalizedUnitCoordinates S) :
    localizedUnitScalar S u ≠ 0 := by
  classical
  unfold localizedUnitScalar
  apply mul_ne_zero
  · cases u.1 <;> norm_num
  · exact Finset.prod_ne_zero_iff.mpr (by
      intro p hp
      exact localizedSignedPrimePower_nonzero (localizedPrimeCoordinate_prime p) (u.2 p))

private lemma localizedSignedPrimePower_neg (p : ℕ) (n : ℤ) :
    localizedSignedPrimePower p (-n) = (localizedSignedPrimePower p n)⁻¹ := by
  by_cases h0 : n = 0
  · subst h0
    simp [localizedSignedPrimePower]
  · by_cases hn : 0 ≤ n
    · have hneg : ¬ 0 ≤ -n := by
        have hn' : 0 < n := lt_of_le_of_ne hn (Ne.symm h0)
        linarith
      simp [localizedSignedPrimePower, hn]
      intro hle
      linarith
    · have hneg : 0 ≤ -n := by
        linarith
      simp [localizedSignedPrimePower, hn]
      intro hpos
      linarith

private lemma localizedUnitScalar_invCoordinates (S : FinitePrimeLocalization)
    (u : LocalizedUnitCoordinates S) :
    localizedUnitScalar S (localizedUnitCoordinatesInv u) = (localizedUnitScalar S u)⁻¹ := by
  classical
  unfold localizedUnitCoordinatesInv localizedUnitScalar
  simp_rw [localizedSignedPrimePower_neg]
  cases u.1 <;> simp [Finset.prod_inv_distrib]

/-- The coordinate model `Bool × (prime coordinates of S → ℤ)` gives explicit supported units in
`ℤ[S⁻¹] ⊆ ℚ`, these units act by additive automorphisms, and the coordinate type is already the
promised `C₂ × ℤ^r` model.
    thm:xi-time-part69-localized-unit-automorphism-group-classification -/
theorem paper_xi_time_part69_localized_unit_automorphism_group_classification
    (S : Omega.Zeta.FinitePrimeLocalization) : LocalizedUnitAutomorphismGroupClassification S := by
  refine ⟨?_, ?_⟩
  · intro u
    have hsupp : denominatorSupportedBy S (localizedUnitScalar S u) :=
      denominatorSupportedBy_localizedUnitScalar S u
    have hne : localizedUnitScalar S u ≠ 0 := localizedUnitScalar_nonzero S u
    have hinv : denominatorSupportedBy S (localizedUnitScalar S u)⁻¹ := by
      rw [← localizedUnitScalar_invCoordinates S u]
      exact denominatorSupportedBy_localizedUnitScalar S (localizedUnitCoordinatesInv u)
    rcases (paper_xi_localized_integers_endomorphism_automorphism_explicit S).2
        ⟨localizedUnitScalar S u, hsupp⟩ hne hinv with ⟨σ, hσ⟩
    exact ⟨hsupp, hne, hinv, σ, hσ⟩
  · exact ⟨Equiv.refl _⟩

end Omega.Zeta
