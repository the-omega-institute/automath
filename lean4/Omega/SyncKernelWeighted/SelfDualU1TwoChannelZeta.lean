import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.SelfDualNormalForm1pmu

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete two-channel datum: a spectral parameter and the self-dual seed block matrix. -/
structure SelfDualU1TwoChannelZetaData where
  z : ℂ
  B0 : SelfDualBlockMatrix

/-- The `u = 1` specialization `B(1)` of the self-dual family. -/
def self_dual_u1_two_channel_zeta_B1 (D : SelfDualU1TwoChannelZetaData) : SelfDualBlockMatrix :=
  selfDualFamily 1 D.B0

/-- Scalar determinant of `I - z B(1)` in the concrete `2 × 2` block presentation. -/
def self_dual_u1_two_channel_zeta_delta (D : SelfDualU1TwoChannelZetaData) : ℂ :=
  let B1 := self_dual_u1_two_channel_zeta_B1 D
  (1 - D.z * B1.X) * (1 - D.z * B1.W) - D.z ^ 2 * B1.Y * B1.Z

/-- The `V₊` channel factor on the unit slice. -/
def self_dual_u1_two_channel_zeta_plus_factor (D : SelfDualU1TwoChannelZetaData) : ℂ :=
  1 - 2 * D.z * D.B0.X

/-- The `V₋` channel factor on the unit slice. -/
def self_dual_u1_two_channel_zeta_minus_factor (D : SelfDualU1TwoChannelZetaData) : ℂ :=
  1 - 2 * D.z * D.B0.W

/-- Full zeta factor at `u = 1`. -/
def self_dual_u1_two_channel_zeta_zeta (D : SelfDualU1TwoChannelZetaData) : ℂ :=
  (self_dual_u1_two_channel_zeta_delta D)⁻¹

/-- The `V₊` channel zeta factor. -/
def self_dual_u1_two_channel_zeta_plus_zeta (D : SelfDualU1TwoChannelZetaData) : ℂ :=
  (self_dual_u1_two_channel_zeta_plus_factor D)⁻¹

/-- The `V₋` channel zeta factor. -/
def self_dual_u1_two_channel_zeta_minus_zeta (D : SelfDualU1TwoChannelZetaData) : ℂ :=
  (self_dual_u1_two_channel_zeta_minus_factor D)⁻¹

/-- Concrete `u = 1` two-channel `Δ/ζ` factorization. -/
def SelfDualU1TwoChannelZetaStatement (D : SelfDualU1TwoChannelZetaData) : Prop :=
  self_dual_u1_two_channel_zeta_delta D =
      self_dual_u1_two_channel_zeta_plus_factor D *
        self_dual_u1_two_channel_zeta_minus_factor D ∧
    self_dual_u1_two_channel_zeta_zeta D =
      self_dual_u1_two_channel_zeta_plus_zeta D *
        self_dual_u1_two_channel_zeta_minus_zeta D

/-- Paper label: `cor:self-dual-u1-two-channel-zeta`. -/
theorem paper_self_dual_u1_two_channel_zeta (D : SelfDualU1TwoChannelZetaData) :
    SelfDualU1TwoChannelZetaStatement D := by
  have hnormal :=
    paper_self_dual_normal_form_1pmu (u := 1) D.B0.X D.B0.Y D.B0.Z D.B0.W
  rcases hnormal with ⟨_, hfamily, _, _⟩
  have hfamily' : selfDualFamily 1 D.B0 = selfDualNormalForm 1 D.B0 := by
    simpa using hfamily
  have hone : ((1 : ℂ) + 1) = 2 := by
    norm_num
  have hB1 :
      self_dual_u1_two_channel_zeta_B1 D =
        { X := 2 * D.B0.X, Y := 0, Z := 0, W := 2 * D.B0.W } := by
    calc
      self_dual_u1_two_channel_zeta_B1 D = selfDualNormalForm 1 D.B0 := by
        simpa [self_dual_u1_two_channel_zeta_B1] using hfamily'
      _ = { X := 2 * D.B0.X, Y := 0, Z := 0, W := 2 * D.B0.W } := by
        exact SelfDualBlockMatrix.ext _ _
          (by simp [selfDualNormalForm, hone])
          (by simp [selfDualNormalForm])
          (by simp [selfDualNormalForm])
          (by simp [selfDualNormalForm, hone])
  have hdelta :
      self_dual_u1_two_channel_zeta_delta D =
        self_dual_u1_two_channel_zeta_plus_factor D *
          self_dual_u1_two_channel_zeta_minus_factor D := by
    rw [self_dual_u1_two_channel_zeta_delta, hB1]
    simp [self_dual_u1_two_channel_zeta_plus_factor, self_dual_u1_two_channel_zeta_minus_factor]
    ring
  refine ⟨hdelta, ?_⟩
  rw [self_dual_u1_two_channel_zeta_zeta, hdelta]
  simp [self_dual_u1_two_channel_zeta_plus_zeta, self_dual_u1_two_channel_zeta_minus_zeta,
    mul_comm]

end

end Omega.SyncKernelWeighted
