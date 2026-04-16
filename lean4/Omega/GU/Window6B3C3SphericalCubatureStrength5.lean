import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.GU.Window6B3C3EuclideanCubature
import Omega.GU.Window6B3C3QuarticRankoneHarmonicDetector

namespace Omega.GU

/-- The `21` labeled spherical atoms used for the window-`6` degree-`5` cubature family:
    `12` long-root directions, `3` negative short-root directions, `3` positive short-root
    directions, and `3` boundary replicas on the positive axes. -/
inductive Window6SphericalLabel where
  | longRoot (plane : Fin 3) (sign : Fin 4)
  | shortNeg (axis : Fin 3)
  | shortPos (axis : Fin 3)
  | boundary (axis : Fin 3)
  deriving DecidableEq

/-- The symmetric degree-`≤ 5` moment constraints reduce to a common long-root weight `λ`,
    a common negative-axis weight `λ / 2`, and a split positive-axis mass `λ / 2`. -/
def Window6DegreeFiveMomentConstraints (c : Window6SphericalLabel → ℂ) : Prop :=
  ∃ lam : ℂ,
    (∀ plane sign, c (.longRoot plane sign) = lam) ∧
      (∀ axis, c (.shortNeg axis) = lam / 2) ∧
      (∀ axis, c (.shortPos axis) + c (.boundary axis) = lam / 2)

/-- The affine family obtained by transferring mass along the three positive coordinate axes. -/
noncomputable def window6DegreeFiveFamilyWeights (lam t₁ t₂ t₃ : ℂ) : Window6SphericalLabel → ℂ
  | .longRoot _ _ => lam
  | .shortNeg _ => lam / 2
  | .shortPos ⟨0, _⟩ => lam / 2 - t₁
  | .shortPos ⟨1, _⟩ => lam / 2 - t₂
  | .shortPos ⟨2, _⟩ => lam / 2 - t₃
  | .boundary ⟨0, _⟩ => t₁
  | .boundary ⟨1, _⟩ => t₂
  | .boundary ⟨2, _⟩ => t₃

/-- Total mass on the `21` labeled spherical support. -/
noncomputable def window6DegreeFiveTotalMass (c : Window6SphericalLabel → ℂ) : ℂ :=
  (∑ plane : Fin 3, ∑ sign : Fin 4, c (.longRoot plane sign)) +
    (∑ axis : Fin 3, c (.shortNeg axis)) +
    (∑ axis : Fin 3, (c (.shortPos axis) + c (.boundary axis)))

/-- Paper-facing degree-`5` spherical cubature family on the `21` labeled window-`6` support:
    the degree-`≤ 5` symmetry constraints are equivalent to three independent boundary-transfer
    parameters, the total mass is always `15 λ`, and the existing quadratic/quartic packages
    remain available unchanged.
    thm:window6-labeled-spherical-degree5-cubature-family -/
theorem paper_window6_labeled_spherical_degree5_cubature_family
    (c : Window6SphericalLabel → ℂ) :
    (Window6DegreeFiveMomentConstraints c ↔
      ∃ lam t₁ t₂ t₃ : ℂ, c = window6DegreeFiveFamilyWeights lam t₁ t₂ t₃) ∧
      (∀ lam t₁ t₂ t₃ : ℂ,
        window6DegreeFiveTotalMass (window6DegreeFiveFamilyWeights lam t₁ t₂ t₃) = 15 * lam) ∧
      (∀ lam t₁ t₂ t₃ : ℂ, ∀ axis : Fin 3,
        (window6DegreeFiveFamilyWeights lam t₁ t₂ t₃ (.shortNeg axis) = lam / 2) ∧
          (window6DegreeFiveFamilyWeights lam t₁ t₂ t₃ (.shortPos axis) +
              window6DegreeFiveFamilyWeights lam t₁ t₂ t₃ (.boundary axis) = lam / 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨lam, hLong, hNeg, hPos⟩
      refine ⟨lam, c (.boundary 0), c (.boundary 1), c (.boundary 2), ?_⟩
      funext lbl
      cases lbl with
      | longRoot plane sign =>
          simp [window6DegreeFiveFamilyWeights, hLong plane sign]
      | shortNeg axis =>
          simp [window6DegreeFiveFamilyWeights, hNeg axis]
      | shortPos axis =>
          have hsplit : c (.shortPos axis) = lam / 2 - c (.boundary axis) := by
            calc
              c (.shortPos axis) = c (.shortPos axis) + c (.boundary axis) - c (.boundary axis) := by
                ring
              _ = lam / 2 - c (.boundary axis) := by
                rw [hPos axis]
          fin_cases axis <;> simpa [window6DegreeFiveFamilyWeights] using hsplit
      | boundary axis =>
          fin_cases axis <;> simp [window6DegreeFiveFamilyWeights]
    · rintro ⟨lam, t₁, t₂, t₃, rfl⟩
      refine ⟨lam, ?_, ?_, ?_⟩
      · intro plane sign
        simp [window6DegreeFiveFamilyWeights]
      · intro axis
        simp [window6DegreeFiveFamilyWeights]
      · intro axis
        fin_cases axis <;> simp [window6DegreeFiveFamilyWeights] <;> ring
  · intro lam t₁ t₂ t₃
    unfold window6DegreeFiveTotalMass
    simp [window6DegreeFiveFamilyWeights, Fin.sum_univ_three]
    ring
  · intro lam t₁ t₂ t₃ axis
    fin_cases axis <;> simp [window6DegreeFiveFamilyWeights] <;> ring

end Omega.GU
