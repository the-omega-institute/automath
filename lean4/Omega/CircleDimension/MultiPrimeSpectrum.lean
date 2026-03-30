import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.CircleDimension

abbrev PrimeSupport := Finset Nat

def multiPrimeSpectrum (supports : Finset PrimeSupport) (J : PrimeSupport) : Nat :=
  (supports.filter fun S => J ⊆ S).card

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

end Omega.CircleDimension
