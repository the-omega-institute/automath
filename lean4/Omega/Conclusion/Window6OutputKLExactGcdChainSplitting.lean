import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Exact-gcd sector masses for the `window-6` output partition
`{S₁, S₃, S₇, S₂₁}`. -/
noncomputable def window6ExactGcdSectorMass : Fin 4 → ℝ
  | 0 => 9 / 16
  | 1 => 9 / 32
  | 2 => 3 / 32
  | _ => 1 / 16

/-- Visible log-ratio contribution on each exact-gcd sector. -/
noncomputable def window6ExactGcdVisibleLogRatio : Fin 4 → ℝ
  | 0 => Real.log (63 / 64 : ℝ)
  | 1 => Real.log (63 / 64 : ℝ)
  | 2 => Real.log (63 / 64 : ℝ)
  | _ => Real.log (21 / 16 : ℝ)

/-- Blind conditional KL contribution on each exact-gcd sector. -/
noncomputable def window6ExactGcdConditionalKl : Fin 4 → ℝ
  | 0 => (5 / 18 : ℝ) * Real.log (32 / 27 : ℝ)
  | 1 => (2 / 9 : ℝ) * Real.log (32 / 27 : ℝ)
  | 2 => (1 / 3 : ℝ) * Real.log (32 / 27 : ℝ)
  | _ => 0

/-- Visible term in the exact-gcd KL chain split. -/
noncomputable def window6ExactGcdVisibleKl : ℝ :=
  ∑ i : Fin 4, window6ExactGcdSectorMass i * window6ExactGcdVisibleLogRatio i

/-- Blind term in the exact-gcd KL chain split. -/
noncomputable def window6ExactGcdBlindKl : ℝ :=
  ∑ i : Fin 4, window6ExactGcdSectorMass i * window6ExactGcdConditionalKl i

/-- Paper-facing exact-gcd chain split for the `window-6` output KL divergence: the visible term
is the coarse exact-gcd contribution, the blind term is the weighted sum of the conditional
sector divergences, and their explicit finite sums collapse to the advertised closed forms.
    thm:conclusion-window6-output-kl-exact-gcd-chain-splitting -/
theorem paper_conclusion_window6_output_kl_exact_gcd_chain_splitting :
    window6ExactGcdVisibleKl =
      (15 / 16 : ℝ) * Real.log (63 / 64 : ℝ) +
        (1 / 16 : ℝ) * Real.log (21 / 16 : ℝ) ∧
    window6ExactGcdBlindKl =
      (1 / 4 : ℝ) * Real.log (32 / 27 : ℝ) ∧
    window6ExactGcdVisibleKl + window6ExactGcdBlindKl =
      (15 / 16 : ℝ) * Real.log (63 / 64 : ℝ) +
        (1 / 16 : ℝ) * Real.log (21 / 16 : ℝ) +
        (1 / 4 : ℝ) * Real.log (32 / 27 : ℝ) := by
  have hVisibleExpand :
      window6ExactGcdVisibleKl =
        (9 / 16 : ℝ) * Real.log (63 / 64 : ℝ) +
          (9 / 32 : ℝ) * Real.log (63 / 64 : ℝ) +
          (3 / 32 : ℝ) * Real.log (63 / 64 : ℝ) +
          (1 / 16 : ℝ) * Real.log (21 / 16 : ℝ) := by
    rw [window6ExactGcdVisibleKl, Fin.sum_univ_four]
    norm_num [window6ExactGcdSectorMass, window6ExactGcdVisibleLogRatio]
  have hBlindExpand :
      window6ExactGcdBlindKl =
        (9 / 16 : ℝ) * ((5 / 18 : ℝ) * Real.log (32 / 27 : ℝ)) +
          (9 / 32 : ℝ) * ((2 / 9 : ℝ) * Real.log (32 / 27 : ℝ)) +
          (3 / 32 : ℝ) * ((1 / 3 : ℝ) * Real.log (32 / 27 : ℝ)) := by
    rw [window6ExactGcdBlindKl, Fin.sum_univ_four]
    norm_num [window6ExactGcdSectorMass, window6ExactGcdConditionalKl]
  have hVisible :
      window6ExactGcdVisibleKl =
        (15 / 16 : ℝ) * Real.log (63 / 64 : ℝ) +
          (1 / 16 : ℝ) * Real.log (21 / 16 : ℝ) := by
    rw [hVisibleExpand]
    ring
  have hBlind :
      window6ExactGcdBlindKl =
        (1 / 4 : ℝ) * Real.log (32 / 27 : ℝ) := by
    rw [hBlindExpand]
    ring
  refine ⟨hVisible, hBlind, ?_⟩
  rw [hVisible, hBlind]

end Omega.Conclusion
