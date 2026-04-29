import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.FoldFrozenMellinStieltjesBifurcation

open Filter
open scoped Topology

namespace Omega.Folding

/-- Concrete asymptotic data for the submaximal recovery-window / frozen-groundstate coexistence
corollary. The recovery window is recorded explicitly by `B`, while the escort side is delegated to
the existing frozen Mellin--Stieltjes bifurcation package. -/
structure FoldSubmaximalRecoveryWindowGroundstateDegeneracyData where
  success : ℕ → ℝ
  beta : ℝ
  B : ℕ → ℕ
  M2 : ℕ → ℝ
  frozenData : FoldFrozenMellinStieltjesBifurcationData
  hB : ∀ m : ℕ, B m = ⌊beta * m⌋₊
  hBetaWindow :
    frozenData.alphaTwo / Real.log 2 < beta ∧ beta < frozenData.alphaStar / Real.log 2
  hEventuallyWindow :
    ∀ᶠ m : ℕ in atTop, M2 m < (2 : ℝ) ^ B m ∧ (2 : ℝ) ^ B m < frozenData.M m
  hEventuallySuccess :
    ∀ᶠ m : ℕ in atTop,
      1 - success m =
        frozenData.K m * (frozenData.M m - (2 : ℝ) ^ B m) / (2 : ℝ) ^ m
  hDeficitTendstoZero :
    Tendsto
      (fun m : ℕ => frozenData.K m * (frozenData.M m - (2 : ℝ) ^ B m) / (2 : ℝ) ^ m)
      atTop (nhds 0)

/-- The concrete oracle-success deficit at the chosen submaximal recovery window. -/
noncomputable def fold_submaximal_recovery_window_groundstate_degeneracy_deficit
    (D : FoldSubmaximalRecoveryWindowGroundstateDegeneracyData) (m : ℕ) : ℝ :=
  D.frozenData.K m * (D.frozenData.M m - (2 : ℝ) ^ D.B m) / (2 : ℝ) ^ m

/-- Publication-facing statement: the explicit dyadic window is the chosen floor profile, it
eventually lies strictly between the second and first multiplicity scales, the corresponding oracle
success converges to `1`, and the frozen escort maximal mass decays with rate `g_*`. -/
def FoldSubmaximalRecoveryWindowGroundstateDegeneracyData.statement
    (D : FoldSubmaximalRecoveryWindowGroundstateDegeneracyData) : Prop :=
  (∀ m : ℕ, D.B m = ⌊D.beta * m⌋₊) ∧
    (∀ᶠ m : ℕ in atTop, D.M2 m < (2 : ℝ) ^ D.B m ∧ (2 : ℝ) ^ D.B m < D.frozenData.M m) ∧
    Tendsto D.success atTop (nhds 1) ∧
    Tendsto
      (fun m : ℕ => (-Real.log (D.frozenData.maxEscortMass m)) / m)
      atTop (nhds D.frozenData.gStar)

/-- Paper label: `cor:fold-submaximal-recovery-window-groundstate-degeneracy`. -/
theorem paper_fold_submaximal_recovery_window_groundstate_degeneracy
    (D : FoldSubmaximalRecoveryWindowGroundstateDegeneracyData) : D.statement := by
  have hdeficit :
      Tendsto (fun m : ℕ => 1 - D.success m) atTop (nhds 0) := by
    have hEq :
        (fun m : ℕ =>
          D.frozenData.K m * (D.frozenData.M m - (2 : ℝ) ^ D.B m) / (2 : ℝ) ^ m) =ᶠ[atTop]
          (fun m : ℕ => 1 - D.success m) := by
      filter_upwards [D.hEventuallySuccess] with m hm
      exact hm.symm
    refine Tendsto.congr' hEq ?_
    exact D.hDeficitTendstoZero
  have hsuccess : Tendsto D.success atTop (nhds 1) := by
    have hsuccess' :
        Tendsto (fun m : ℕ => (1 : ℝ) - (1 - D.success m)) atTop (nhds ((1 : ℝ) - 0)) :=
      tendsto_const_nhds.sub hdeficit
    have hrew :
        (fun m : ℕ => 1 - (1 - D.success m)) = D.success := by
      funext m
      ring_nf
    rw [← hrew]
    simpa using hsuccess'
  have hfrozen := paper_fold_frozen_mellin_stieltjes_bifurcation D.frozenData
  exact ⟨D.hB, D.hEventuallyWindow, hsuccess, hfrozen.2.2⟩

end Omega.Folding
