import Omega.Zeta.XiJDiscriminantElliptic2TorsionMobius
import Mathlib.Tactic

namespace Omega.Zeta

/-- The quadratic branch factor in the original `t`-coordinate. -/
def xiJDiscriminantQuadratic (t : ℚ) : ℚ :=
  t ^ 2 + 1862 * t + 161792

/-- A normalized Möbius candidate exchanging `1728` with infinity. -/
def xiJNormalizedMobius (a b t : ℚ) : ℚ :=
  a + b / (t - 1728)

/-- Three rational image constraints pin down the normalized candidate. -/
def xiJThreePointConstraints (a b : ℚ) : Prop :=
  xiJNormalizedMobius a b 1729 = xiJTwoTorsionMobius 1729 ∧
    xiJNormalizedMobius a b 1730 = xiJTwoTorsionMobius 1730 ∧
    xiJNormalizedMobius a b 1732 = xiJTwoTorsionMobius 1732

/-- Rigidity of the normalized Möbius form together with the two covariance identities used in the
paper: the shifted-coordinate normalization and the quadratic-branch covariance. -/
def xiJMobiusRigidityCovariance : Prop :=
  (∀ a b : ℚ, xiJThreePointConstraints a b →
    ∀ t : ℚ, xiJNormalizedMobius a b t = xiJTwoTorsionMobius t) ∧
  (∀ t : ℚ, xiJTwoTorsionMobius t - 1728 = 6365312 / (t - 1728)) ∧
  (∀ t : ℚ, t ≠ 1728 →
    xiJDiscriminantQuadratic (xiJTwoTorsionMobius t) =
      6365312 * xiJDiscriminantQuadratic t / (t - 1728) ^ 2)

private lemma xiJ_normalized_rigidity (a b : ℚ) (h : xiJThreePointConstraints a b) :
    ∀ t : ℚ, xiJNormalizedMobius a b t = xiJTwoTorsionMobius t := by
  rcases h with ⟨h1729, h1730, _h1732⟩
  have h1 := h1729
  have h2 := h1730
  norm_num [xiJNormalizedMobius, xiJTwoTorsionMobius] at h1 h2
  have h1 : a + b = 6367040 := by
    exact h1
  have h2 : a + b / 2 = 3184384 := by
    exact h2
  have hb : b = 6365312 := by
    linarith
  have ha : a = 1728 := by
    linarith
  intro t
  simp [xiJNormalizedMobius, xiJTwoTorsionMobius, ha, hb]

private lemma xiJ_shift_covariance (t : ℚ) :
    xiJTwoTorsionMobius t - 1728 = 6365312 / (t - 1728) := by
  unfold xiJTwoTorsionMobius
  ring_nf

private lemma xiJ_shifted_quadratic_covariance (u : ℚ) (hu : u ≠ 0) :
    xiJShiftedBranchQuadratic (6365312 / u) =
      6365312 * xiJShiftedBranchQuadratic u / u ^ 2 := by
  unfold xiJShiftedBranchQuadratic
  field_simp [hu]
  ring_nf

private lemma xiJ_quadratic_covariance (t : ℚ) (ht : t ≠ 1728) :
    xiJDiscriminantQuadratic (xiJTwoTorsionMobius t) =
      6365312 * xiJDiscriminantQuadratic t / (t - 1728) ^ 2 := by
  have hu : t - 1728 ≠ 0 := sub_ne_zero.mpr ht
  have hQ (s : ℚ) : xiJDiscriminantQuadratic s = xiJShiftedBranchQuadratic (s - 1728) := by
    unfold xiJDiscriminantQuadratic xiJShiftedBranchQuadratic
    ring_nf
  calc
    xiJDiscriminantQuadratic (xiJTwoTorsionMobius t)
        = xiJShiftedBranchQuadratic (xiJTwoTorsionMobius t - 1728) := by
            rw [hQ]
    _ = xiJShiftedBranchQuadratic (6365312 / (t - 1728)) := by
      rw [xiJ_shift_covariance]
    _ = 6365312 * xiJShiftedBranchQuadratic (t - 1728) / (t - 1728) ^ 2 := by
      exact xiJ_shifted_quadratic_covariance (t - 1728) hu
    _ = 6365312 * xiJDiscriminantQuadratic t / (t - 1728) ^ 2 := by
      rw [← hQ]

/-- The explicit `2`-torsion Möbius transform is rigid inside the normalized family determined by
the three prescribed rational images, and it satisfies the shifted-coordinate and quadratic-branch
covariance identities.
    prop:xi-j-discriminant-mobius-rigidity-covariance -/
theorem paper_xi_j_discriminant_mobius_rigidity_covariance : xiJMobiusRigidityCovariance := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b h
    exact xiJ_normalized_rigidity a b h
  · exact xiJ_shift_covariance
  · exact xiJ_quadratic_covariance

end Omega.Zeta
