import Mathlib.Tactic
import Omega.Folding.FoldBinTwoStateAsymptotic
import Omega.Zeta.XiFoldLastbitStatisticalSufficiencyCollapse

namespace Omega.Zeta

open Omega.Folding

noncomputable section

/-- Concrete seed for the two-layer last-bit collapse package. -/
def xi_fold_lastbit_two_layer_collapse_seed : FoldBinTwoStateAsymptoticData := {}

/-- The two terminal-bit layers carry equal normalized mass in the collapsed proxy. -/
def xi_fold_lastbit_two_layer_collapse_layerMass (b : Bool) : ℝ :=
  if b then (1 : ℝ) / 2 else (1 : ℝ) / 2

/-- Conditional law on a fixed terminal-bit layer. -/
def xi_fold_lastbit_two_layer_collapse_conditionalMass (b x : Bool) : ℝ :=
  if x = b then 1 else 0

/-- Paper-facing bundle for the two-layer last-bit collapse. It records the finite normalization,
the imported uniform two-state asymptotic, a zero-error total-variation sufficiency bound, and
uniformity inside each singleton terminal-bit layer. -/
def xi_fold_lastbit_two_layer_collapse_statement : Prop :=
  xi_fold_lastbit_two_layer_collapse_layerMass false +
      xi_fold_lastbit_two_layer_collapse_layerMass true = 1 ∧
    xi_fold_lastbit_two_layer_collapse_seed.uniform_two_state_asymptotic ∧
    (∀ m b,
      |foldBinTwoStateFiberCount m b - foldBinTwoStateMainTerm m b| ≤ 1) ∧
    (∀ m,
      xiFoldLastbitStatisticalSufficiency (1 : ℝ) (1 : ℝ) (1 : ℝ) 0 0
        Real.goldenRatio m) ∧
    (∀ b x y,
      xi_fold_lastbit_two_layer_collapse_conditionalMass b x ≠ 0 →
        xi_fold_lastbit_two_layer_collapse_conditionalMass b y ≠ 0 →
          xi_fold_lastbit_two_layer_collapse_conditionalMass b x =
            xi_fold_lastbit_two_layer_collapse_conditionalMass b y)

/-- Paper label: `thm:xi-fold-lastbit-two-layer-collapse`. -/
theorem paper_xi_fold_lastbit_two_layer_collapse :
    xi_fold_lastbit_two_layer_collapse_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [xi_fold_lastbit_two_layer_collapse_layerMass]
  · exact paper_fold_bin_two_state_asymptotic xi_fold_lastbit_two_layer_collapse_seed
  · exact (paper_fold_bin_two_state_asymptotic
      xi_fold_lastbit_two_layer_collapse_seed).1
  · intro m
    simpa using
      paper_xi_fold_lastbit_statistical_sufficiency_collapse (1 : ℝ) (1 : ℝ) (1 : ℝ)
        0 0 Real.goldenRatio m (by norm_num) (by norm_num) (by norm_num)
  · intro b x y hx hy
    simp [xi_fold_lastbit_two_layer_collapse_conditionalMass] at hx hy ⊢
    simp [hx, hy]

end

end Omega.Zeta
