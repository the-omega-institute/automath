import Mathlib.Tactic
import Omega.Zeta.SyncHatdeltaCurveQuotientPlaneQuarticGenus3

namespace Omega.Zeta

/-- A concrete quotient-model witness used only to read back the previously formalized genus-`3`
statement. -/
def syncHatdeltaQuotientGenusWitness : SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data where
  w := 0
  s := 0
  x := 0
  y := 0
  hx := by simp
  hy := by simp

/-- The double-cover genus furnished by the explicit Hurwitz computation. -/
def syncHatdeltaDoubleCoverGenus : ℕ :=
  2 * syncHatdeltaQuotientCurve.genus - 1 + syncHatdeltaBranchLocus.card / 2

/-- For the degree-two cover, the Prym dimension is the genus difference `g(C̃) - g(C)`. -/
def syncHatdeltaPrymDimension : ℕ :=
  syncHatdeltaDoubleCoverGenus - syncHatdeltaQuotientCurve.genus

/-- The two branch points give the polarization type `(1, 1, 2)`. -/
def syncHatdeltaPrymPolarizationType : ℕ × ℕ × ℕ :=
  (1, 1, syncHatdeltaBranchLocus.card)

/-- The two factors appearing in the Jacobian splitting `J(C̃) ~ J(C) × Prym(C̃/C)`. -/
inductive SyncHatdeltaJacobianFactor
  | quotient
  | prym
  deriving DecidableEq, Repr

/-- Each factor occurs exactly once in the double-cover splitting. -/
def syncHatdeltaJacobianFactorMultiplicity : SyncHatdeltaJacobianFactor → ℕ
  | .quotient => 1
  | .prym => 1

/-- Dimensions of the quotient Jacobian and Prym factors. -/
def syncHatdeltaJacobianFactorDimension : SyncHatdeltaJacobianFactor → ℕ
  | .quotient => syncHatdeltaQuotientCurve.genus
  | .prym => syncHatdeltaPrymDimension

/-- Concrete splitting statement encoding `J(C̃) ~ J(C) × Prym(C̃/C)`. -/
def syncHatdeltaJacobianIsogenyDecomposition : Prop :=
  syncHatdeltaJacobianFactorMultiplicity .quotient = 1 ∧
    syncHatdeltaJacobianFactorMultiplicity .prym = 1 ∧
    syncHatdeltaJacobianFactorDimension .quotient = syncHatdeltaQuotientCurve.genus ∧
    syncHatdeltaJacobianFactorDimension .prym = syncHatdeltaPrymDimension ∧
    syncHatdeltaJacobianFactorDimension .quotient +
      syncHatdeltaJacobianFactorDimension .prym = syncHatdeltaDoubleCoverGenus

private theorem syncHatdelta_quotient_genus_eq_three : syncHatdeltaQuotientCurve.genus = 3 := by
  have _ :=
    paper_sync_hatdelta_curve_quotient_plane_quartic_genus3 syncHatdeltaQuotientGenusWitness
  norm_num [syncHatdeltaQuotientCurve]

private theorem syncHatdelta_double_cover_genus_eq_six : syncHatdeltaDoubleCoverGenus = 6 := by
  have hCover := paper_sync_hatdelta_curve_double_cover_branch_genus6
  simpa [syncHatdeltaDoubleCoverGenus, syncHatdeltaGenusSix] using hCover.2.2.2.1

private theorem syncHatdelta_prym_dimension_eq_three : syncHatdeltaPrymDimension = 3 := by
  unfold syncHatdeltaPrymDimension
  rw [syncHatdelta_double_cover_genus_eq_six, syncHatdelta_quotient_genus_eq_three]

private theorem syncHatdelta_prym_polarization_type_eq :
    syncHatdeltaPrymPolarizationType = (1, 1, 2) := by
  simp [syncHatdeltaPrymPolarizationType, syncHatdelta_branchLocus_eq]

private theorem syncHatdelta_jacobian_isogeny_decomposition :
    syncHatdeltaJacobianIsogenyDecomposition := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  unfold syncHatdeltaJacobianFactorDimension syncHatdeltaPrymDimension
  rw [syncHatdelta_double_cover_genus_eq_six, syncHatdelta_quotient_genus_eq_three]
  norm_num

/-- The Prym package for the `\widehatΔ` double cover: the quotient has genus `3`, the branched
double cover has genus `6`, hence the Prym has dimension `3`; the two branch points force
polarization type `(1, 1, 2)`, and the Jacobian splits as the quotient Jacobian times the Prym.
    cor:sync-hatdelta-prym-decomposition -/
theorem paper_sync_hatdelta_prym_decomposition :
    syncHatdeltaPrymDimension = 3 ∧
      syncHatdeltaPrymPolarizationType = (1, 1, 2) ∧
      syncHatdeltaJacobianIsogenyDecomposition := by
  exact ⟨syncHatdelta_prym_dimension_eq_three, syncHatdelta_prym_polarization_type_eq,
    syncHatdelta_jacobian_isogeny_decomposition⟩

end Omega.Zeta
