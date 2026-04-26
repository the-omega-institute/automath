import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.POM.KCollisionRootFilter
import Omega.Zeta.XiMittagLefflerKfoldZeroQuantization

namespace Omega.POM

open Omega.Zeta

/-- The dominant oscillatory phase carried by the conjugate root pair in the `E_{k,k}` model. -/
noncomputable def pom_kcollision_ekk_root_phase_quantization_phase (k : ℕ) (r : ℝ) : ℝ :=
  r * Real.sin (Real.pi / (k : ℝ)) + Real.pi / (k : ℝ)

/-- The radius solving the model phase equation
`r * sin (π / k) + π / k = (n + 1/2) π`. -/
noncomputable def pom_kcollision_ekk_root_phase_quantization_quantized_radius
    (k n : ℕ) : ℝ :=
  (((n : ℝ) + (1 / 2 : ℝ) - 1 / (k : ℝ)) * Real.pi) / Real.sin (Real.pi / (k : ℝ))

/-- Lean-side `E_{k,k}` quantization package: the root-filter seeds give the required sign
pattern, the simple-zero Mittag-Leffler wrapper gives the dominant coefficient and the bounded
remainder, and the explicit phase equation is solved by the quantized radius above. -/
def pom_kcollision_ekk_root_phase_quantization_statement : Prop :=
  ((-1 : ℤ) ^ 2 = 1 ∧ (-1 : ℤ) ^ 3 = -1) ∧
    ∀ k n : ℕ, ∀ u C ρ : ℝ, 2 ≤ k → 0 < u → |ρ| ≤ 1 →
      xiJordanUniversalKernelCoeff k 1 u =
          (-u) / (Nat.factorial (pomKCollisionMittagLefflerOrder k 1) : ℝ) ∧
        |xiJordanFullFamily k 1 n u C ρ - xiJordanDominantBlockCoeff k 1 n u| ≤ |C| ∧
        pom_kcollision_ekk_root_phase_quantization_phase k
            (pom_kcollision_ekk_root_phase_quantization_quantized_radius k n) =
          ((n : ℝ) + (1 / 2 : ℝ)) * Real.pi

/-- Paper label: `thm:pom-kcollision-ekk-root-phase-quantization`. The root-filter recurrence
supplies the parity signs, the universal `k`-fold Jordan-collision package supplies the
Mittag-Leffler simple-zero coefficient and the exponentially bounded remainder, and the displayed
phase equation is then solved explicitly by the quantized radius. -/
theorem paper_pom_kcollision_ekk_root_phase_quantization :
    pom_kcollision_ekk_root_phase_quantization_statement := by
  rcases paper_pom_kcollision_root_filter_recurrence_package with ⟨_, _, _, _, _, hsign⟩
  refine ⟨hsign, ?_⟩
  intro k n u C ρ hk _hu hρ
  rcases Omega.Zeta.paper_xi_mittag_leffler_kfold_zero_quantization k n u C ρ hρ with
    ⟨hcoeff, _, _, hbound⟩
  have hkpos_nat : 0 < k := by omega
  have hkgt_nat : 1 < k := by omega
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkpos_nat
  have hkgt : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hkgt_nat
  have hdiv_pos : 0 < Real.pi / (k : ℝ) := by positivity
  have hdiv_lt_pi : Real.pi / (k : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hkpos]
    nlinarith [Real.pi_pos, hkgt]
  have hsin_pos : 0 < Real.sin (Real.pi / (k : ℝ)) := by
    exact Real.sin_pos_of_pos_of_lt_pi hdiv_pos hdiv_lt_pi
  refine ⟨hcoeff, hbound, ?_⟩
  unfold pom_kcollision_ekk_root_phase_quantization_phase
    pom_kcollision_ekk_root_phase_quantization_quantized_radius
  field_simp [hkpos.ne', hsin_pos.ne']
  ring

end Omega.POM
