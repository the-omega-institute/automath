import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Conclusion.BinfoldCollisionScaleForcesMaxfiberDivergence

namespace Omega.Conclusion

open scoped BigOperators

/-- The nonzero Fourier excess `W_m = M_m Col_m - 1`. -/
def conclusion_fourier_excess_complete_delocalization_W (M Col : ℕ → ℝ) (m : ℕ) : ℝ :=
  binfoldCollisionScaleTerm M Col m - 1

/-- The participation ratio `Π_m = W_m² / ∑_k E_m(k)^2`, with the zero-denominator case folded back
to `W_m`. -/
noncomputable def conclusion_fourier_excess_complete_delocalization_Pi
    (energyCount : ℕ → ℕ) (energy : ∀ m, Fin (energyCount m) → ℝ) (M Col : ℕ → ℝ) (m : ℕ) :
    ℝ :=
  let W := conclusion_fourier_excess_complete_delocalization_W M Col m
  let denom : ℝ := ∑ i, (energy m i) ^ (2 : ℕ)
  if denom = 0 then W else W ^ (2 : ℕ) / denom

private theorem conclusion_fourier_excess_complete_delocalization_W_diverges
    (M Col : ℕ → ℝ)
    (hGrowth : NatDivergesToInfinity (binfoldCollisionScaleTerm M Col)) :
    NatDivergesToInfinity (conclusion_fourier_excess_complete_delocalization_W M Col) := by
  intro K
  obtain ⟨m, hm⟩ := hGrowth (K + 1)
  refine ⟨m, ?_⟩
  have hm' : (K : ℝ) + 1 ≤ binfoldCollisionScaleTerm M Col m := by
    simpa [Nat.cast_add] using hm
  dsimp [conclusion_fourier_excess_complete_delocalization_W]
  linarith

private theorem conclusion_fourier_excess_complete_delocalization_W_nonneg
    (energyCount : ℕ → ℕ) (energy : ∀ m, Fin (energyCount m) → ℝ) (M Col : ℕ → ℝ)
    (hParseval :
      ∀ m, (∑ i, energy m i) = conclusion_fourier_excess_complete_delocalization_W M Col m)
    (hNonneg : ∀ m i, 0 ≤ energy m i) (m : ℕ) :
    0 ≤ conclusion_fourier_excess_complete_delocalization_W M Col m := by
  calc
    0 ≤ ∑ i, energy m i := Finset.sum_nonneg fun i _ => hNonneg m i
    _ = conclusion_fourier_excess_complete_delocalization_W M Col m := hParseval m

private theorem conclusion_fourier_excess_complete_delocalization_denom_le_W
    (energyCount : ℕ → ℕ) (energy : ∀ m, Fin (energyCount m) → ℝ) (M Col : ℕ → ℝ)
    (hParseval :
      ∀ m, (∑ i, energy m i) = conclusion_fourier_excess_complete_delocalization_W M Col m)
    (hNonneg : ∀ m i, 0 ≤ energy m i) (hLeOne : ∀ m i, energy m i ≤ 1) (m : ℕ) :
    (∑ i, (energy m i) ^ (2 : ℕ)) ≤ conclusion_fourier_excess_complete_delocalization_W M Col m := by
  calc
    ∑ i, (energy m i) ^ (2 : ℕ) ≤ ∑ i, energy m i := by
      refine Finset.sum_le_sum fun i _ => ?_
      nlinarith [hNonneg m i, hLeOne m i]
    _ = conclusion_fourier_excess_complete_delocalization_W M Col m := hParseval m

private theorem conclusion_fourier_excess_complete_delocalization_W_le_Pi
    (energyCount : ℕ → ℕ) (energy : ∀ m, Fin (energyCount m) → ℝ) (M Col : ℕ → ℝ)
    (hParseval :
      ∀ m, (∑ i, energy m i) = conclusion_fourier_excess_complete_delocalization_W M Col m)
    (hNonneg : ∀ m i, 0 ≤ energy m i) (hLeOne : ∀ m i, energy m i ≤ 1) (m : ℕ) :
    conclusion_fourier_excess_complete_delocalization_W M Col m ≤
      conclusion_fourier_excess_complete_delocalization_Pi energyCount energy M Col m := by
  set W : ℝ := conclusion_fourier_excess_complete_delocalization_W M Col m
  set denom : ℝ := ∑ i, (energy m i) ^ (2 : ℕ)
  have hW_nonneg : 0 ≤ W := by
    subst W
    exact conclusion_fourier_excess_complete_delocalization_W_nonneg
      energyCount energy M Col hParseval hNonneg m
  have hdenom_nonneg : 0 ≤ denom := by
    subst denom
    exact Finset.sum_nonneg fun i _ => by positivity
  have hdenom_le_W : denom ≤ W := by
    subst denom W
    exact conclusion_fourier_excess_complete_delocalization_denom_le_W
      energyCount energy M Col hParseval hNonneg hLeOne m
  by_cases hdenom : denom = 0
  · simp [conclusion_fourier_excess_complete_delocalization_Pi, W, denom, hdenom]
  · have hdenom_pos : 0 < denom := lt_of_le_of_ne hdenom_nonneg (Ne.symm hdenom)
    have hmul : W * denom ≤ W * W := mul_le_mul_of_nonneg_left hdenom_le_W hW_nonneg
    have hdiv : W * denom / denom ≤ (W * W) / denom := by
      exact div_le_div_of_nonneg_right hmul hdenom_nonneg
    have hineq : W ≤ W ^ (2 : ℕ) / denom := by
      calc
        W = W * denom / denom := by
          field_simp [hdenom]
        _ ≤ (W * W) / denom := hdiv
        _ = W ^ (2 : ℕ) / denom := by ring
    simpa [conclusion_fourier_excess_complete_delocalization_Pi, W, denom, hdenom] using hineq

/-- Paper label: `thm:conclusion-fourier-excess-complete-delocalization`.

If the nonzero Fourier energy package realizes the Parseval excess `W_m = M_m Col_m - 1`, every
mode energy lies in `[0,1]`, and the collision scale `M_m Col_m` is unbounded, then `W_m`
diverges, the participation ratio satisfies `Π_m ≥ W_m` pointwise, and therefore `Π_m` also
diverges. -/
theorem paper_conclusion_fourier_excess_complete_delocalization
    (energyCount : ℕ → ℕ) (energy : ∀ m, Fin (energyCount m) → ℝ) (M Col : ℕ → ℝ)
    (hParseval :
      ∀ m, (∑ i, energy m i) = conclusion_fourier_excess_complete_delocalization_W M Col m)
    (hNonneg : ∀ m i, 0 ≤ energy m i) (hLeOne : ∀ m i, energy m i ≤ 1)
    (hGrowth : NatDivergesToInfinity (binfoldCollisionScaleTerm M Col)) :
    NatDivergesToInfinity (conclusion_fourier_excess_complete_delocalization_W M Col) ∧
      (∀ m,
        conclusion_fourier_excess_complete_delocalization_W M Col m ≤
          conclusion_fourier_excess_complete_delocalization_Pi energyCount energy M Col m) ∧
      NatDivergesToInfinity
        (conclusion_fourier_excess_complete_delocalization_Pi energyCount energy M Col) := by
  have hWDiv :
      NatDivergesToInfinity (conclusion_fourier_excess_complete_delocalization_W M Col) :=
    conclusion_fourier_excess_complete_delocalization_W_diverges M Col hGrowth
  refine ⟨hWDiv, ?_, ?_⟩
  · intro m
    exact conclusion_fourier_excess_complete_delocalization_W_le_Pi
      energyCount energy M Col hParseval hNonneg hLeOne m
  · intro K
    obtain ⟨m, hm⟩ := hWDiv K
    exact ⟨m, hm.trans (conclusion_fourier_excess_complete_delocalization_W_le_Pi
      energyCount energy M Col hParseval hNonneg hLeOne m)⟩

end Omega.Conclusion
