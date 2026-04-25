import Omega.CircleDimension.MultiPrimeSpectrum

namespace Omega.CircleDimension

/-- A local finite-support model for the direct sum of localized rank-one summands. -/
def cdim_multiprime_divisible_spectrum_explicit_finite_direct_sum_model
    (supports : Finset PrimeSupport) : Finset PrimeSupport :=
  supports

/-- In the finite support model, the `p`-divisible summands are exactly those whose support
contains `p`. -/
def cdim_multiprime_divisible_spectrum_explicit_p_divisible
    (S : PrimeSupport) (p : Nat) : Prop :=
  p ∈ S

/-- A summand is `J`-divisible exactly when every prime in `J` is in its support. -/
def cdim_multiprime_divisible_spectrum_explicit_j_divisible
    (S J : PrimeSupport) : Prop :=
  J ⊆ S

/-- The explicit spectrum counts the direct-sum summands whose supports contain `J`. -/
noncomputable def cdim_multiprime_divisible_spectrum_explicit_spectrum
    (supports : Finset PrimeSupport) (J : PrimeSupport) : Nat :=
  by
    classical
    exact
      ((cdim_multiprime_divisible_spectrum_explicit_finite_direct_sum_model supports).filter
        fun S => cdim_multiprime_divisible_spectrum_explicit_j_divisible S J).card

def cdim_multiprime_divisible_spectrum_explicit_statement : Prop :=
  (∀ supports J,
    cdim_multiprime_divisible_spectrum_explicit_spectrum supports J =
      (supports.filter fun S => J ⊆ S).card) ∧
  (∀ supports J,
    cdim_multiprime_divisible_spectrum_explicit_spectrum supports J =
      multiPrimeSpectrum supports J) ∧
  (∀ (supports supports' : Finset PrimeSupport) (J : PrimeSupport)
      (e : PrimeSupport ≃ PrimeSupport),
    (∀ S, S ∈ supports' ↔ e.symm S ∈ supports) →
    (∀ S, cdim_multiprime_divisible_spectrum_explicit_j_divisible (e S) J ↔
      cdim_multiprime_divisible_spectrum_explicit_j_divisible S J) →
    cdim_multiprime_divisible_spectrum_explicit_spectrum supports J =
      cdim_multiprime_divisible_spectrum_explicit_spectrum supports' J)

lemma cdim_multiprime_divisible_spectrum_explicit_j_divisible_iff_subset
    (S J : PrimeSupport) :
    cdim_multiprime_divisible_spectrum_explicit_j_divisible S J ↔ J ⊆ S := by
  rfl

lemma cdim_multiprime_divisible_spectrum_explicit_spectrum_eq_count
    (supports : Finset PrimeSupport) (J : PrimeSupport) :
    cdim_multiprime_divisible_spectrum_explicit_spectrum supports J =
      (supports.filter fun S => J ⊆ S).card := by
  unfold cdim_multiprime_divisible_spectrum_explicit_spectrum
    cdim_multiprime_divisible_spectrum_explicit_finite_direct_sum_model
  congr 1
  ext S
  simp [cdim_multiprime_divisible_spectrum_explicit_j_divisible_iff_subset]

lemma cdim_multiprime_divisible_spectrum_explicit_spectrum_iso
    (supports supports' : Finset PrimeSupport) (J : PrimeSupport)
    (e : PrimeSupport ≃ PrimeSupport)
    (hmem : ∀ S, S ∈ supports' ↔ e.symm S ∈ supports)
    (hdiv : ∀ S, cdim_multiprime_divisible_spectrum_explicit_j_divisible (e S) J ↔
      cdim_multiprime_divisible_spectrum_explicit_j_divisible S J) :
    cdim_multiprime_divisible_spectrum_explicit_spectrum supports J =
      cdim_multiprime_divisible_spectrum_explicit_spectrum supports' J := by
  unfold cdim_multiprime_divisible_spectrum_explicit_spectrum
    cdim_multiprime_divisible_spectrum_explicit_finite_direct_sum_model
  refine Finset.card_bij (fun S _ => e S) ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter] at hS ⊢
    refine ⟨?_, ?_⟩
    · rw [hmem (e S)]
      simpa using hS.1
    · exact (hdiv S).mpr hS.2
  · intro S₁ hS₁ S₂ hS₂ hEq
    exact e.injective hEq
  · intro T hT
    refine ⟨e.symm T, ?_, by simp⟩
    simp only [Finset.mem_filter] at hT ⊢
    refine ⟨?_, ?_⟩
    · exact (hmem T).mp hT.1
    · have h := (hdiv (e.symm T)).mp
      simpa using h (by simpa using hT.2)

/-- Paper label: `prop:cdim-multiprime-divisible-spectrum-explicit`. -/
theorem paper_cdim_multiprime_divisible_spectrum_explicit :
    cdim_multiprime_divisible_spectrum_explicit_statement := by
  refine ⟨?_, ?_, ?_⟩
  · exact cdim_multiprime_divisible_spectrum_explicit_spectrum_eq_count
  · intro supports J
    rw [cdim_multiprime_divisible_spectrum_explicit_spectrum_eq_count]
    exact (multiPrimeSpectrum_eq_count supports J).symm
  · exact cdim_multiprime_divisible_spectrum_explicit_spectrum_iso

end Omega.CircleDimension
