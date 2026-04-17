import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Conclusion.Window6Collision

namespace Omega.Conclusion

noncomputable section

/-- The four-point spectrum `{0, 2, 3, 4}` contributes the following scalar coefficients in the
window-6 hidden-sector heat semigroup decomposition. -/
def window6HeatSemigroupScalars (t : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (1, Real.exp (-2 * t), Real.exp (-3 * t), Real.exp (-4 * t))

/-- The optimal global cooling rate is the lowest positive spectral shell `2`. -/
def window6GlobalCoolingRate (t : ℝ) : ℝ := Real.exp (-2 * t)

/-- Removing the `2`-shell raises the cooling rate to the next shell `3`. -/
def window6HiddenCoolingRate (t : ℝ) : ℝ := Real.exp (-3 * t)

/-- Hidden heat trace from multiplicities `(8, 8, 27)` on the positive spectral shells. -/
def window6HiddenHeatTrace (t : ℝ) : ℝ :=
  8 * Real.exp (-2 * t) + 8 * Real.exp (-3 * t) + 27 * Real.exp (-4 * t)

/-- Hidden spectral zeta function attached to the same three positive shells. -/
def window6HiddenSpectralZeta (s : ℝ) : ℝ :=
  8 * Real.rpow 2 (-s) + 8 * Real.rpow 3 (-s) + 27 * Real.rpow 4 (-s)

/-- The positive-shell multiplicities for the concrete window-6 hidden spectrum. -/
def window6SpectralMultiplicity : ℕ → ℕ
  | 2 => 8
  | 3 => 8
  | 4 => 27
  | _ => 0

/-- The hidden pseudodeterminant written in product form over the positive shells. -/
def window6HiddenPseudodeterminant : ℕ := 2 ^ 8 * 3 ^ 8 * 4 ^ 27

/-- Window-6 hidden-sector three-temperature cooling and spectral-holography package.
    thm:conclusion-window6-three-temperature-hidden-cooling-spectral-holography -/
theorem paper_conclusion_window6_three_temperature_hidden_cooling_spectral_holography :
    (∀ t : ℝ,
      window6HeatSemigroupScalars t =
        (1, Real.exp (-2 * t), Real.exp (-3 * t), Real.exp (-4 * t))) ∧
      (∀ t : ℝ,
        window6GlobalCoolingRate t = Real.exp (-2 * t) ∧
          window6HiddenCoolingRate t = Real.exp (-3 * t)) ∧
      (∀ t s : ℝ,
        window6HiddenHeatTrace t =
            8 * Real.exp (-2 * t) + 8 * Real.exp (-3 * t) + 27 * Real.exp (-4 * t) ∧
          window6HiddenSpectralZeta s =
            8 * Real.rpow 2 (-s) + 8 * Real.rpow 3 (-s) + 27 * Real.rpow 4 (-s) ∧
          window6HiddenPseudodeterminant = 2 ^ 62 * 3 ^ 8) ∧
      (cBinFiberHist 6 2 = window6SpectralMultiplicity 2 ∧
        cBinFiberHist 6 3 = window6SpectralMultiplicity 3 / 2 ∧
        cBinFiberHist 6 4 = window6SpectralMultiplicity 4 / 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    rfl
  · intro t
    exact ⟨rfl, rfl⟩
  · intro t s
    refine ⟨rfl, rfl, ?_⟩
    unfold window6HiddenPseudodeterminant
    norm_num [pow_mul, pow_add]
  · refine ⟨cBinFiberHist_6_2, ?_, ?_⟩
    · norm_num [window6SpectralMultiplicity, cBinFiberHist_6_3]
    · norm_num [window6SpectralMultiplicity, cBinFiberHist_6_4]

end

end Omega.Conclusion
