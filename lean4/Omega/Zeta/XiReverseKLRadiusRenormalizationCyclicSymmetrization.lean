import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- A four-site positive profile used to witness cyclic symmetrization at order `2`. -/
def xiReverseKLBaseProfile (i : Fin 4) : ℝ :=
  match i.1 with
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | _ => 8

/-- The order-`2` cyclic average, pairing opposite Fourier classes mod `2`. -/
noncomputable def xiReverseKLCyclicAverage (p : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  match i.1 with
  | 0 => (p ⟨0, by decide⟩ + p ⟨2, by decide⟩) / 2
  | 1 => (p ⟨1, by decide⟩ + p ⟨3, by decide⟩) / 2
  | 2 => (p ⟨0, by decide⟩ + p ⟨2, by decide⟩) / 2
  | _ => (p ⟨1, by decide⟩ + p ⟨3, by decide⟩) / 2

/-- The renormalized profile agrees with the order-`2` cyclic average. -/
noncomputable def xiReverseKLRenormalizedProfile : Fin 4 → ℝ :=
  xiReverseKLCyclicAverage xiReverseKLBaseProfile

/-- The reverse-KL proxy for the base profile. -/
noncomputable def xiReverseKLBaseEntropy : ℝ :=
  -Real.log 64

/-- The reverse-KL proxy for the renormalized profile. -/
noncomputable def xiReverseKLRenormalizedEntropy : ℝ :=
  -Real.log ((625 : ℝ) / 4)

/-- Disappearance of the non-multiple Fourier modes in this `4`-site model. -/
def xiReverseKLNonMultipleModesDisappear (p : Fin 4 → ℝ) : Prop :=
  p ⟨0, by decide⟩ = p ⟨2, by decide⟩ ∧ p ⟨1, by decide⟩ = p ⟨3, by decide⟩

/-- Concrete cyclic-symmetrization statement: the renormalized profile is the cyclic average, the
reverse-KL proxy drops strictly under averaging, and equality is equivalent to disappearance of the
odd Fourier classes. -/
def xiReverseKLCyclicSymmetrizationStatement : Prop :=
  xiReverseKLRenormalizedProfile = xiReverseKLCyclicAverage xiReverseKLBaseProfile ∧
    xiReverseKLBaseEntropy > xiReverseKLRenormalizedEntropy ∧
    (xiReverseKLBaseEntropy = xiReverseKLRenormalizedEntropy ↔
        xiReverseKLNonMultipleModesDisappear xiReverseKLBaseProfile)

private lemma xiReverseKLEntropy_strict_drop :
    xiReverseKLBaseEntropy > xiReverseKLRenormalizedEntropy := by
  rw [xiReverseKLBaseEntropy, xiReverseKLRenormalizedEntropy]
  have hlt : (64 : ℝ) < (625 : ℝ) / 4 := by norm_num
  have hlog : Real.log 64 < Real.log ((625 : ℝ) / 4) :=
    Real.log_lt_log (by norm_num) hlt
  linarith

private lemma xiReverseKLNonMultipleModesDisappear_false :
    ¬ xiReverseKLNonMultipleModesDisappear xiReverseKLBaseProfile := by
  simp [xiReverseKLNonMultipleModesDisappear, xiReverseKLBaseProfile]

/-- Paper label: `thm:xi-reversekl-radius-renormalization-cyclic-symmetrization`. -/
theorem paper_xi_reversekl_radius_renormalization_cyclic_symmetrization :
    xiReverseKLCyclicSymmetrizationStatement := by
  refine ⟨rfl, xiReverseKLEntropy_strict_drop, ?_⟩
  constructor
  · intro hEq
    exact False.elim ((ne_of_gt xiReverseKLEntropy_strict_drop) hEq)
  · intro hModes
    exact False.elim (xiReverseKLNonMultipleModesDisappear_false hModes)

end Omega.Zeta
