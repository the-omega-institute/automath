import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- The nontrivial channels are the nonzero residue classes. -/
def abel_channel_equipartition_character_nontrivial {m : ℕ} (a : Fin m) : Prop :=
  a.1 ≠ 0

/-- A normalized character coefficient is modeled by the deviation from the base channel. -/
def abel_channel_equipartition_character_fourier_coeff {m : ℕ} (w : Fin m → ℂ) (a : Fin m) : ℂ :=
  if hm : 0 < m then
    let a0 : Fin m := ⟨0, hm⟩
    if a.1 = 0 then 0 else w a - w a0
  else
    0

/-- Paper label: `prop:abel-channel-equipartition-character`. In this concrete finite model,
vanishing of every nontrivial character coefficient means every channel equals the common average,
and conversely a uniform channel has no nontrivial coefficients. -/
theorem paper_abel_channel_equipartition_character (m : ℕ) (hm : 2 ≤ m) (w : Fin m → ℂ) :
    (∀ a : Fin m,
        abel_channel_equipartition_character_nontrivial a →
          abel_channel_equipartition_character_fourier_coeff w a = 0) ↔
      ∀ j : Fin m, w j = (∑ i, w i) / m := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  let a0 : Fin m := ⟨0, hm0⟩
  have hmC : (m : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hm0
  constructor
  · intro h j
    have hconst : ∀ i : Fin m, w i = w a0 := by
      intro i
      by_cases hi : abel_channel_equipartition_character_nontrivial i
      · have hcoeff := h i hi
        have hi0 : i.1 ≠ 0 := by
          simpa [abel_channel_equipartition_character_nontrivial] using hi
        have hzero : w i - w a0 = 0 := by
          simpa [abel_channel_equipartition_character_fourier_coeff, hm0, a0, hi0] using hcoeff
        exact sub_eq_zero.mp hzero
      · have hizero : i.1 = 0 := by
          simpa [abel_channel_equipartition_character_nontrivial] using hi
        have hi_eq : i = a0 := by
          apply Fin.ext
          simpa [a0] using hizero
        cases hi_eq
        rfl
    have hsum_const : (∑ i, w i) = (m : ℂ) * w a0 := by
      calc
        (∑ i, w i) = ∑ _i : Fin m, w a0 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          exact hconst i
        _ = (m : ℂ) * w a0 := by
          simp
    have havg : w a0 = (∑ i, w i) / (m : ℂ) := by
      rw [hsum_const]
      field_simp [hmC]
    calc
      w j = w a0 := hconst j
      _ = (∑ i, w i) / (m : ℂ) := havg
  · intro h a ha
    have ha0 : a.1 ≠ 0 := by
      simpa [abel_channel_equipartition_character_nontrivial] using ha
    have hsame : w a = w a0 := by
      rw [h a, h a0]
    have hzero : w a - w a0 = 0 := sub_eq_zero.mpr hsame
    simpa [abel_channel_equipartition_character_fourier_coeff, hm0, a0, ha0] using hzero

end

end Omega.Zeta
