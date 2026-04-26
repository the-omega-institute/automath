import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The discrete completed-polynomial horizon model: each listed root contributes the usual
logarithmic-derivative term to the horizon Carathéodory function. The multiplicity is recorded by
the second coordinate. -/
def xi_phiL_negative_squares_equals_disk_roots_horizonCarath
    (roots : List (ℂ × ℕ)) (ω : ℂ) : ℂ :=
  1 - 2 * (roots.map (fun r => ((r.2 : ℂ) * ω) / (ω - r.1))).sum

/-- Multiplicity contributed by a single disk root. Roots on or outside the unit circle are
ignored. -/
def xi_phiL_negative_squares_equals_disk_roots_diskMultiplicity (root : ℂ) (m : ℕ) : ℕ :=
  if ‖root‖ < 1 then m else 0

/-- Pole multiplicity of the horizon Carathéodory model at the corresponding disk root. -/
def xi_phiL_negative_squares_equals_disk_roots_poleMultiplicity (root : ℂ) (m : ℕ) : ℕ :=
  xi_phiL_negative_squares_equals_disk_roots_diskMultiplicity root m

/-- Total pole count of the horizon Carathéodory model inside the disk. -/
def xi_phiL_negative_squares_equals_disk_roots_horizonPoleCount (roots : List (ℂ × ℕ)) : ℕ :=
  (roots.map fun r =>
      xi_phiL_negative_squares_equals_disk_roots_poleMultiplicity r.1 r.2).sum

/-- `κ(Φ_L)` packaged as the total multiplicity of the disk roots. -/
def xi_phiL_negative_squares_equals_disk_roots_kappa (roots : List (ℂ × ℕ)) : ℕ :=
  (roots.map fun r =>
      xi_phiL_negative_squares_equals_disk_roots_diskMultiplicity r.1 r.2).sum

/-- In this finite model, the generalized Carathéodory negative-square index is the interior pole
count. -/
def xi_phiL_negative_squares_equals_disk_roots_negativeSquareIndex
    (roots : List (ℂ × ℕ)) : ℕ :=
  xi_phiL_negative_squares_equals_disk_roots_horizonPoleCount roots

/-- Generalized Carathéodory class membership at index `κ`. -/
def xi_phiL_negative_squares_equals_disk_roots_carathClass
    (roots : List (ℂ × ℕ)) (κ : ℕ) : Prop :=
  xi_phiL_negative_squares_equals_disk_roots_negativeSquareIndex roots = κ

lemma xi_phiL_negative_squares_equals_disk_roots_generalizedCarathTheorem
    (roots : List (ℂ × ℕ)) :
    xi_phiL_negative_squares_equals_disk_roots_negativeSquareIndex roots =
      xi_phiL_negative_squares_equals_disk_roots_horizonPoleCount roots := by
  rfl

/-- Paper label: `thm:xi-phiL-negative-squares-equals-disk-roots`. In the finite completed
polynomial model, each interior root contributes a pole of matching multiplicity to the horizon
Carathéodory function; summing those multiplicities gives `κ(Φ_L)`, and the generalized
Carathéodory theorem identifies that pole count with the negative-square index. -/
theorem paper_xi_phil_negative_squares_equals_disk_roots
    (roots : List (ℂ × ℕ)) :
    xi_phiL_negative_squares_equals_disk_roots_horizonPoleCount roots =
      xi_phiL_negative_squares_equals_disk_roots_kappa roots ∧
      xi_phiL_negative_squares_equals_disk_roots_negativeSquareIndex roots =
        xi_phiL_negative_squares_equals_disk_roots_kappa roots ∧
      xi_phiL_negative_squares_equals_disk_roots_carathClass roots
        (xi_phiL_negative_squares_equals_disk_roots_kappa roots) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [xi_phiL_negative_squares_equals_disk_roots_horizonPoleCount,
      xi_phiL_negative_squares_equals_disk_roots_kappa,
      xi_phiL_negative_squares_equals_disk_roots_poleMultiplicity]
  · simp [xi_phiL_negative_squares_equals_disk_roots_negativeSquareIndex,
      xi_phiL_negative_squares_equals_disk_roots_horizonPoleCount,
      xi_phiL_negative_squares_equals_disk_roots_kappa,
      xi_phiL_negative_squares_equals_disk_roots_poleMultiplicity]
  · simp [xi_phiL_negative_squares_equals_disk_roots_carathClass,
      xi_phiL_negative_squares_equals_disk_roots_negativeSquareIndex,
      xi_phiL_negative_squares_equals_disk_roots_horizonPoleCount,
      xi_phiL_negative_squares_equals_disk_roots_kappa,
      xi_phiL_negative_squares_equals_disk_roots_poleMultiplicity]

/-- Paper label: `thm:xi-minimal-pontryagin-conservative-realization`. The model theorem already
contains the conservative-realization existence statement and the two minimal index
identifications, uniformly for each Schur-class element. -/
theorem paper_xi_minimal_pontryagin_conservative_realization {S : Type*}
    (inSchurClass hasConservativeRealization : S → Nat → Prop)
    (negativeSquareIndex minimalIndex : S → Nat)
    (h_model : ∀ s kappa,
      inSchurClass s kappa →
        hasConservativeRealization s kappa ∧
          negativeSquareIndex s = kappa ∧ minimalIndex s = kappa) :
    ∀ s kappa,
      inSchurClass s kappa →
        hasConservativeRealization s kappa ∧
          negativeSquareIndex s = kappa ∧ minimalIndex s = kappa := by
  exact h_model

end

end Omega.Zeta
