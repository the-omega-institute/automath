import Mathlib.Data.Rat.Sqrt
import Mathlib.Tactic

namespace Omega.Zeta

/-- Shifted coordinate centered at the rational `2`-torsion point `t = 1728`. -/
def xiJShiftedCoordinate (t : ℚ) : ℚ :=
  t - 1728

/-- The quadratic factor in the shifted `u = t - 1728` model of the discriminant elliptic curve. -/
def xiJShiftedBranchQuadratic (u : ℚ) : ℚ :=
  u ^ 2 + 5318 * u + 6365312

/-- The same quadratic written back in the original `t`-coordinate. -/
def xiJBranchQuadratic (t : ℚ) : ℚ :=
  xiJShiftedBranchQuadratic (xiJShiftedCoordinate t)

/-- Translation by the rational `2`-torsion point in shifted coordinates. -/
def xiJShiftedTranslation (u : ℚ) : ℚ :=
  6365312 / u

/-- The corresponding Möbius involution in the original `t`-coordinate. -/
def xiJTwoTorsionMobius (t : ℚ) : ℚ :=
  1728 + 6365312 / (t - 1728)

/-- Explicit `u = t - 1728` translation law for the rational `2`-torsion Möbius map. -/
def xiJExplicitTranslationLaw (t : ℚ) : Prop :=
  xiJShiftedCoordinate (xiJTwoTorsionMobius t) = xiJShiftedTranslation (xiJShiftedCoordinate t)

/-- The Möbius transform is an involution and has no rational fixed points. -/
def xiJInvolutionWithoutFixedPoints (t : ℚ) : Prop :=
  xiJTwoTorsionMobius (xiJTwoTorsionMobius t) = t ∧ xiJTwoTorsionMobius t ≠ t

/-- The quadratic branch points are exchanged by the shifted translation law. -/
def xiJBranchPointSwap : Prop :=
  ∀ u : ℚ, xiJShiftedBranchQuadratic u = 0 →
    xiJShiftedBranchQuadratic (xiJShiftedTranslation u) = 0

private lemma xiJShiftedTranslation_sq_ne_branch_constant (u : ℚ) :
    u ^ 2 ≠ (6365312 : ℚ) := by
  intro hu
  have hsquare : Rat.sqrt (6365312 : ℚ) * Rat.sqrt (6365312 : ℚ) = (6365312 : ℚ) :=
    (Rat.exists_mul_self (6365312 : ℚ)).1 ⟨u, by simpa [pow_two] using hu⟩
  norm_num at hsquare

private lemma xiJExplicitTranslationLaw_proof (t : ℚ) :
    xiJExplicitTranslationLaw t := by
  unfold xiJExplicitTranslationLaw xiJShiftedCoordinate xiJTwoTorsionMobius xiJShiftedTranslation
  ring_nf

private lemma xiJShiftedTranslation_involutive (u : ℚ) (hu : u ≠ 0) :
    xiJShiftedTranslation (xiJShiftedTranslation u) = u := by
  unfold xiJShiftedTranslation
  field_simp [hu]

private lemma xiJInvolution_proof (t : ℚ) (ht : t ≠ 1728) :
    xiJTwoTorsionMobius (xiJTwoTorsionMobius t) = t := by
  have hu0 : xiJShiftedCoordinate t ≠ 0 := sub_ne_zero.mpr ht
  have hShift :
      xiJShiftedCoordinate (xiJTwoTorsionMobius (xiJTwoTorsionMobius t)) =
        xiJShiftedCoordinate t := by
    calc
      xiJShiftedCoordinate (xiJTwoTorsionMobius (xiJTwoTorsionMobius t))
          = xiJShiftedTranslation (xiJShiftedCoordinate (xiJTwoTorsionMobius t)) :=
            xiJExplicitTranslationLaw_proof (xiJTwoTorsionMobius t)
      _ = xiJShiftedTranslation (xiJShiftedTranslation (xiJShiftedCoordinate t)) := by
        rw [xiJExplicitTranslationLaw_proof t]
      _ = xiJShiftedCoordinate t := xiJShiftedTranslation_involutive (xiJShiftedCoordinate t) hu0
  unfold xiJShiftedCoordinate at hShift
  linarith

private lemma xiJMobius_ne_self (t : ℚ) (ht : t ≠ 1728) :
    xiJTwoTorsionMobius t ≠ t := by
  intro hFix
  have hTrans := xiJExplicitTranslationLaw_proof t
  have hu :
      xiJShiftedCoordinate t = xiJShiftedTranslation (xiJShiftedCoordinate t) := by
    calc
      xiJShiftedCoordinate t = xiJShiftedCoordinate (xiJTwoTorsionMobius t) := by simp [hFix]
      _ = xiJShiftedTranslation (xiJShiftedCoordinate t) := hTrans
  have hu0 : xiJShiftedCoordinate t ≠ 0 := sub_ne_zero.mpr ht
  have hsq : xiJShiftedCoordinate t ^ 2 = (6365312 : ℚ) := by
    have hmul : (6365312 : ℚ) = xiJShiftedCoordinate t * xiJShiftedCoordinate t := by
      simpa [xiJShiftedTranslation] using (div_eq_iff hu0).mp hu.symm
    simpa [pow_two, mul_comm] using hmul.symm
  exact xiJShiftedTranslation_sq_ne_branch_constant (xiJShiftedCoordinate t) hsq

private lemma xiJBranchPointSwap_proof :
    xiJBranchPointSwap := by
  intro u hu
  simp only [xiJShiftedBranchQuadratic] at hu
  have hu0 : u ≠ 0 := by
    intro hz
    rw [hz] at hu
    norm_num at hu
  have hu' : u ^ 2 = -5318 * u - 6365312 := by
    linarith
  simp only [xiJShiftedBranchQuadratic, xiJShiftedTranslation]
  field_simp [hu0]
  nlinarith [hu']

/-- Translation by the rational `2`-torsion point becomes an explicit Möbius involution after the
shift `u = t - 1728`; the map is involutive, has no rational fixed point, and exchanges the
quadratic branch packet of the discriminant model.
    thm:xi-j-discriminant-elliptic-2torsion-mobius -/
theorem paper_xi_j_discriminant_elliptic_2torsion_mobius (t : ℚ) (ht : t ≠ 1728) :
    xiJExplicitTranslationLaw t ∧
      xiJInvolutionWithoutFixedPoints t ∧
      xiJBranchPointSwap := by
  refine ⟨xiJExplicitTranslationLaw_proof t, ?_, xiJBranchPointSwap_proof⟩
  exact ⟨xiJInvolution_proof t ht, xiJMobius_ne_self t ht⟩

end Omega.Zeta
