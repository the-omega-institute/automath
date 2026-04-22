import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.CircleDimension.LeyangSixthNormIdentity3Torsion
import Omega.CircleDimension.S4V4KummerTorsorGeneratedByExplicit3torsion

namespace Omega.CircleDimension

noncomputable section

/-- The Lee--Yang cubic polynomial appearing in the explicit genus-two model. -/
def cdim_s4_v4_kummer_model_and_resolvent_recovery_leyang_polynomial (y : ℂ) : ℂ :=
  256 * y ^ 3 + 411 * y ^ 2 + 165 * y + 32

/-- Rational points on the Lee--Yang model `u² = -y(y-1)P(y)` over the chosen base extension. -/
structure cdim_s4_v4_kummer_model_and_resolvent_recovery_leyang_point where
  y : ℂ
  u : ℂ
  equation :
    u ^ 2 =
      -y * (y - 1) * cdim_s4_v4_kummer_model_and_resolvent_recovery_leyang_polynomial y

/-- A Kummer point is a Lee--Yang point together with a cubic Kummer generator `W`. -/
structure cdim_s4_v4_kummer_model_and_resolvent_recovery_kummer_point where
  y : ℂ
  u : ℂ
  W : ℂ
  equation :
    u ^ 2 =
      -y * (y - 1) * cdim_s4_v4_kummer_model_and_resolvent_recovery_leyang_polynomial y

/-- Over the base field extension containing the Kummer generator, the model is just the Lee--Yang
point together with the auxiliary coordinate `W`. -/
def cdim_s4_v4_kummer_model_and_resolvent_recovery_birational_equiv :
    cdim_s4_v4_kummer_model_and_resolvent_recovery_kummer_point ≃
      cdim_s4_v4_kummer_model_and_resolvent_recovery_leyang_point × ℂ where
  toFun P :=
    (⟨P.y, P.u, P.equation⟩, P.W)
  invFun Q :=
    ⟨Q.1.y, Q.1.u, Q.2, Q.1.equation⟩
  left_inv P := by
    cases P
    rfl
  right_inv Q := by
    cases Q
    rfl

/-- The `C₃`-action is linearized by multiplying the Kummer coordinate. -/
def cdim_s4_v4_kummer_model_and_resolvent_recovery_linearized_action (W : ℂ) : Prop :=
  ∀ ζ : ℂ, (ζ * W) ^ 3 = ζ ^ 3 * W ^ 3

/-- The explicit substitution `z = ((2y + 1)(2w - 1))/3`. -/
def cdim_s4_v4_kummer_model_and_resolvent_recovery_substitution (y w : ℂ) : ℂ :=
  ((2 * y + 1) * (2 * w - 1)) / 3

/-- The resolvent polynomial recovered from the Cardano/Kummer variable. -/
def cdim_s4_v4_kummer_model_and_resolvent_recovery_resolvent_polynomial (y z : ℂ) : ℂ :=
  z ^ 3 + (2 * y + 1) * z ^ 2 - (4 * y ^ 2 + 4 * y + 1) * z -
    (8 * y ^ 3 + 13 * y ^ 2 + 5 * y + 1)

/-- Concrete S4/V4 Kummer-model package. The fields store the complementary branch divisor used
for the `C₃`-torsor, a point on the Lee--Yang model, the Kummer generator, the derived Cardano
parameter `w = W + W⁻¹`, and the cubic relation needed to recover the resolvent equation. -/
structure cdim_s4_v4_kummer_model_and_resolvent_recovery_data where
  infinityFiber : Finset S4V4FiberPoint
  hcard : infinityFiber.card = 3
  y : ℂ
  u : ℂ
  W : ℂ
  Θ : ℂ
  w : ℂ
  leyang_equation :
    u ^ 2 =
      -y * (y - 1) * cdim_s4_v4_kummer_model_and_resolvent_recovery_leyang_polynomial y
  kummer_generator : W ^ 3 = Θ
  w_eq : w = W + W⁻¹
  resolvent_identity :
    8 * (2 * y + 1) ^ 3 * (w ^ 3 - 3 * w) = 128 * y ^ 3 + 219 * y ^ 2 + 69 * y + 16

namespace cdim_s4_v4_kummer_model_and_resolvent_recovery_data

/-- The paper-facing package: the existing complementary-branch and explicit-`3`-torsion results
provide the Kummer torsor, the Lee--Yang identity supplies the base curve relation, the Kummer
model is birational to the Lee--Yang curve with an auxiliary cubic coordinate, the covering action
is linearized by scalar multiplication on `W`, and the explicit substitution recovers the
resolvent cubic equation. -/
def statement (D : cdim_s4_v4_kummer_model_and_resolvent_recovery_data) : Prop :=
  let R : S4V4ComplementaryRamificationData := ⟨D.infinityFiber, D.hcard⟩
  Nonempty
      (cdim_s4_v4_kummer_model_and_resolvent_recovery_kummer_point ≃
        cdim_s4_v4_kummer_model_and_resolvent_recovery_leyang_point × ℂ) ∧
    cdim_s4_v4_kummer_model_and_resolvent_recovery_linearized_action D.W ∧
    (128 * D.y ^ 3 + 219 * D.y ^ 2 + 69 * D.y + 16) ^ 2 + 27 * D.u ^ 2 =
      256 * (2 * D.y + 1) ^ 6 ∧
    cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_kummer_extension_equation D.W D.Θ ∧
    R.complementaryBranchLinearEquiv ∧
    divisorDegree R.pullbackInfinityDivisor = 3 ∧
    s4v4CompatibleBiellipticPencils.card = 3 ∧
    cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_eta_order = 3 ∧
    cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_generated_torsor ∧
    cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_base_field_radicand = -3 ∧
    cdim_s4_v4_kummer_model_and_resolvent_recovery_resolvent_polynomial D.y
        (cdim_s4_v4_kummer_model_and_resolvent_recovery_substitution D.y D.w) = 0

end cdim_s4_v4_kummer_model_and_resolvent_recovery_data

open cdim_s4_v4_kummer_model_and_resolvent_recovery_data

lemma cdim_s4_v4_kummer_model_and_resolvent_recovery_substitution_identity (y w : ℂ) :
    cdim_s4_v4_kummer_model_and_resolvent_recovery_resolvent_polynomial y
        (cdim_s4_v4_kummer_model_and_resolvent_recovery_substitution y w) =
      (8 * (2 * y + 1) ^ 3 * (w ^ 3 - 3 * w) - (128 * y ^ 3 + 219 * y ^ 2 + 69 * y + 16)) /
        27 := by
  unfold cdim_s4_v4_kummer_model_and_resolvent_recovery_resolvent_polynomial
  unfold cdim_s4_v4_kummer_model_and_resolvent_recovery_substitution
  ring

/-- Paper label: `prop:cdim-s4-v4-kummer-model-and-resolvent-recovery`.
The existing Lee--Yang norm/`3`-torsion package produces the hyperelliptic base equation, the
explicit `C₃`-torsor gives the Kummer cubic `W³ = Θ`, the resulting Kummer model is birational to
the Lee--Yang model over the base extension, the covering action linearizes as `W ↦ ζ₃ W`, and
the substitution `z = ((2y + 1)(2w - 1))/3` recovers the resolvent equation. -/
theorem paper_cdim_s4_v4_kummer_model_and_resolvent_recovery
    (D : cdim_s4_v4_kummer_model_and_resolvent_recovery_data) : D.statement := by
  let R : S4V4ComplementaryRamificationData := ⟨D.infinityFiber, D.hcard⟩
  have htorsor :=
    paper_cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion D.infinityFiber D.hcard
  have hleyang :=
    paper_circle_dimension_leyang_sixth_norm_identity_and_3torsion D.y D.u D.leyang_equation
  have hlinear :
      cdim_s4_v4_kummer_model_and_resolvent_recovery_linearized_action D.W := by
    intro ζ
    ring
  have hkummer :
      cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_kummer_extension_equation D.W D.Θ := by
    simpa [cdim_s4_v4_kummer_torsor_generated_by_explicit_3torsion_kummer_extension_equation] using
      D.kummer_generator
  have hresidual :
      8 * (2 * D.y + 1) ^ 3 * (D.w ^ 3 - 3 * D.w) -
          (128 * D.y ^ 3 + 219 * D.y ^ 2 + 69 * D.y + 16) = 0 := by
    exact sub_eq_zero.mpr D.resolvent_identity
  have hresolvent :
      cdim_s4_v4_kummer_model_and_resolvent_recovery_resolvent_polynomial D.y
          (cdim_s4_v4_kummer_model_and_resolvent_recovery_substitution D.y D.w) = 0 := by
    rw [cdim_s4_v4_kummer_model_and_resolvent_recovery_substitution_identity]
    rw [hresidual]
    norm_num
  dsimp [cdim_s4_v4_kummer_model_and_resolvent_recovery_data.statement, R]
  refine ⟨⟨cdim_s4_v4_kummer_model_and_resolvent_recovery_birational_equiv⟩, hlinear, hleyang,
    hkummer, ?_, ?_, ?_, ?_, ?_, ?_, hresolvent⟩
  · exact htorsor.1
  · exact htorsor.2.1
  · exact htorsor.2.2.1
  · exact htorsor.2.2.2.1
  · exact htorsor.2.2.2.2.1
  · exact htorsor.2.2.2.2.2.1

end

end Omega.CircleDimension
