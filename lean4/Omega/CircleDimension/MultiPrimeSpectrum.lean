import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.CircleDimension

abbrev PrimeSupport := Finset Nat

def multiPrimeSpectrum (supports : Finset PrimeSupport) (J : PrimeSupport) : Nat :=
  (supports.filter fun S => J ⊆ S).card

/-- Type count n_A(J): exact-support multiplicity.
    thm:cdim-mobius-inversion-localization-multiset-classification -/
def typeCount (supports : Finset PrimeSupport) (J : PrimeSupport) : Nat :=
  (supports.filter fun S => S = J).card

/-- Explicit count formula for the divisible multiprime spectrum.
    prop:cdim-multiprime-divisible-spectrum-explicit -/
theorem multiPrimeSpectrum_eq_count (supports : Finset PrimeSupport) (J : PrimeSupport) :
    multiPrimeSpectrum supports J = (supports.filter fun S => J ⊆ S).card := rfl

/-- Antitone in the prime support parameter.
    prop:cdim-multiprime-divisible-spectrum-explicit -/
theorem multiPrimeSpectrum_anti_mono {supports : Finset PrimeSupport} {J K : PrimeSupport}
    (hJK : J ⊆ K) :
    multiPrimeSpectrum supports K ≤ multiPrimeSpectrum supports J := by
  unfold multiPrimeSpectrum
  apply Finset.card_le_card
  intro S hS
  simp only [Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, fun x hxJ => hS.2 (hJK hxJ)⟩

/-- Empty support is counted by every support set.
    prop:cdim-multiprime-divisible-spectrum-explicit -/
theorem multiPrimeSpectrum_empty (supports : Finset PrimeSupport) :
    multiPrimeSpectrum supports ∅ = supports.card := by
  unfold multiPrimeSpectrum
  simp

/-- Any support counts itself, hence contributes positive spectrum mass.
    prop:cdim-multiprime-divisible-spectrum-explicit -/
theorem multiPrimeSpectrum_pos_of_mem {supports : Finset PrimeSupport} {J : PrimeSupport}
    (hJ : J ∈ supports) :
    0 < multiPrimeSpectrum supports J := by
  unfold multiPrimeSpectrum
  apply Finset.card_pos.mpr
  refine ⟨J, ?_⟩
  simp [hJ]

/-- Zeta-transform identity: the spectrum is the finite sum of exact-support counts.
    thm:cdim-mobius-inversion-localization-multiset-classification -/
theorem multiPrimeSpectrum_eq_sum_typeCount
    (supports : Finset PrimeSupport) (J : PrimeSupport) :
    multiPrimeSpectrum supports J =
      Finset.sum supports (fun K => if J ⊆ K then typeCount supports K else 0) := by
  have htc : ∀ {K : PrimeSupport}, K ∈ supports → typeCount supports K = 1 := by
    intro K hK
    unfold typeCount
    have hEq : supports.filter (fun S => S = K) = {K} := by
      ext x
      constructor
      · intro hx
        simp only [Finset.mem_filter, Finset.mem_singleton] at hx ⊢
        exact hx.2
      · intro hx
        simp only [Finset.mem_filter, Finset.mem_singleton] at hx ⊢
        subst hx
        exact ⟨hK, rfl⟩
    rw [hEq]
    simp
  unfold multiPrimeSpectrum
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro K hK
  by_cases hJK : J ⊆ K
  · simp [hJK, htc hK]
  · simp [hJK]

/-- Total type count equals the total number of supports.
    thm:cdim-mobius-inversion-localization-multiset-classification -/
theorem sum_typeCount_eq_card (supports : Finset PrimeSupport) :
    Finset.sum supports (typeCount supports) = supports.card := by
  have htc : ∀ {K : PrimeSupport}, K ∈ supports → typeCount supports K = 1 := by
    intro K hK
    unfold typeCount
    have hEq : supports.filter (fun S => S = K) = {K} := by
      ext x
      constructor
      · intro hx
        simp only [Finset.mem_filter, Finset.mem_singleton] at hx ⊢
        exact hx.2
      · intro hx
        simp only [Finset.mem_filter, Finset.mem_singleton] at hx ⊢
        subst hx
        exact ⟨hK, rfl⟩
    rw [hEq]
    simp
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl ?_
  intro K hK
  simp [htc hK]

end Omega.CircleDimension
