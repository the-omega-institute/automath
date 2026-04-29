import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import Omega.Zeta.XiLimitDefectPotentialRationalization

namespace Omega.Zeta

open Complex

/-- The sign factor appearing in the explicit Fourier-side formula. -/
noncomputable def xi_limit_defect_potential_fourier_injective_sign (ξ : ℝ) : ℝ :=
  if ξ < 0 then -1 else if ξ = 0 then 0 else 1

/-- The explicit derivative of one defect packet kernel. -/
noncomputable def xi_limit_defect_potential_fourier_injective_packet_derivative
    (P : XiLimitDefectPacket) (x : ℝ) : ℝ :=
  (x - P.γ) / ((x - P.γ) ^ 2 + (1 + P.δ.1) ^ 2) -
    (x - P.γ) / ((x - P.γ) ^ 2 + (1 - P.δ.1) ^ 2)

/-- The derivative of the finite defect potential obtained by summing the packet derivatives. -/
noncomputable def xi_limit_defect_potential_fourier_injective_potential_derivative :
    List XiLimitDefectPacket → ℝ → ℝ
  | [], _ => 0
  | P :: Ps, x =>
      (P.m : ℝ) * xi_limit_defect_potential_fourier_injective_packet_derivative P x +
        xi_limit_defect_potential_fourier_injective_potential_derivative Ps x

/-- One explicit Fourier-side packet contribution. -/
noncomputable def xi_limit_defect_potential_fourier_injective_packet_fourier
    (P : XiLimitDefectPacket) (ξ : ℝ) : ℂ :=
  (-Complex.I) * ((Real.pi * xi_limit_defect_potential_fourier_injective_sign ξ : ℝ) : ℂ) *
    (((Real.exp (-(1 + P.δ.1) * |ξ|) - Real.exp (-(1 - P.δ.1) * |ξ|) : ℝ) : ℂ) *
      Complex.exp (-((P.γ * ξ : ℝ) : ℂ) * Complex.I))

/-- The explicit Fourier-side model obtained by summing the packet contributions termwise. -/
noncomputable def xi_limit_defect_potential_fourier_injective_fourier_model :
    List XiLimitDefectPacket → ℝ → ℂ
  | [], _ => 0
  | P :: Ps, ξ =>
      (P.m : ℂ) * xi_limit_defect_potential_fourier_injective_packet_fourier P ξ +
        xi_limit_defect_potential_fourier_injective_fourier_model Ps ξ

lemma xi_limit_defect_potential_fourier_injective_packet_kernel_lt_one
    (P : XiLimitDefectPacket) (x : ℝ) :
    xiRealQuadraticFactor P x < 1 := by
  unfold xiRealQuadraticFactor
  have hδ : 0 < P.δ.1 := P.δ.2.1
  have hden :
      0 < (x - P.γ) ^ 2 + (1 + P.δ.1) ^ 2 := by
    have hsquare : 0 < (1 + P.δ.1) ^ 2 := by
      positivity
    nlinarith [sq_nonneg (x - P.γ)]
  have hnum_lt_den :
      (x - P.γ) ^ 2 + (1 - P.δ.1) ^ 2 < (x - P.γ) ^ 2 + (1 + P.δ.1) ^ 2 := by
    nlinarith [hδ]
  exact (div_lt_one hden).2 hnum_lt_den

lemma xi_limit_defect_potential_fourier_injective_packet_kernel_pos
    (P : XiLimitDefectPacket) (x : ℝ) :
    0 < xiPacketKernel P x := by
  have hpos : 0 < xiRealQuadraticFactor P x := xiRealQuadraticFactor_pos P x
  have hlt : xiRealQuadraticFactor P x < 1 :=
    xi_limit_defect_potential_fourier_injective_packet_kernel_lt_one P x
  have hlog : Real.log (xiRealQuadraticFactor P x) < 0 := by
    have : Real.log (xiRealQuadraticFactor P x) < Real.log 1 :=
      Real.log_lt_log hpos hlt
    simpa using this
  unfold xiPacketKernel
  nlinarith

lemma xi_limit_defect_potential_fourier_injective_packet_kernel_nonneg
    (P : XiLimitDefectPacket) (x : ℝ) :
    0 ≤ xiPacketKernel P x := by
  exact le_of_lt (xi_limit_defect_potential_fourier_injective_packet_kernel_pos P x)

lemma xi_limit_defect_potential_fourier_injective_packet_kernel_eq
    (P : XiLimitDefectPacket) :
    xiPacketKernel P =
      fun x =>
        (1 / 2 : ℝ) * Real.log ((x - P.γ) ^ 2 + (1 + P.δ.1) ^ 2) -
          (1 / 2 : ℝ) * Real.log ((x - P.γ) ^ 2 + (1 - P.δ.1) ^ 2) := by
  funext x
  have hnum :
      ((x - P.γ) ^ 2 + (1 - P.δ.1) ^ 2) ≠ 0 := by
    exact ne_of_gt <| by
      have hsquare : 0 < (1 - P.δ.1) ^ 2 := by
        have hminus : 0 < 1 - P.δ.1 := sub_pos.mpr P.δ.2.2
        exact sq_pos_of_pos hminus
      nlinarith [sq_nonneg (x - P.γ)]
  have hden :
      ((x - P.γ) ^ 2 + (1 + P.δ.1) ^ 2) ≠ 0 := by
    exact ne_of_gt <| by
      have hplus : 0 < 1 + P.δ.1 := by linarith [P.δ.2.1]
      have hsquare : 0 < (1 + P.δ.1) ^ 2 := sq_pos_of_pos hplus
      nlinarith [sq_nonneg (x - P.γ)]
  unfold xiPacketKernel xiRealQuadraticFactor
  rw [Real.log_div hnum hden]
  ring

lemma xi_limit_defect_potential_fourier_injective_packet_hasDerivAt
    (P : XiLimitDefectPacket) (x : ℝ) :
    HasDerivAt (xiPacketKernel P)
      (xi_limit_defect_potential_fourier_injective_packet_derivative P x) x := by
  have hkernel :=
    xi_limit_defect_potential_fourier_injective_packet_kernel_eq P
  let gPlus : ℝ → ℝ := fun y => (y - P.γ) ^ 2 + (1 + P.δ.1) ^ 2
  let gMinus : ℝ → ℝ := fun y => (y - P.γ) ^ 2 + (1 - P.δ.1) ^ 2
  have hgPlus : HasDerivAt gPlus (2 * (x - P.γ)) x := by
    dsimp [gPlus]
    simpa using ((((hasDerivAt_id x).sub_const P.γ).pow 2).add_const ((1 + P.δ.1) ^ 2))
  have hgMinus : HasDerivAt gMinus (2 * (x - P.γ)) x := by
    dsimp [gMinus]
    simpa using ((((hasDerivAt_id x).sub_const P.γ).pow 2).add_const ((1 - P.δ.1) ^ 2))
  have hgPlus_ne : gPlus x ≠ 0 := by
    dsimp [gPlus]
    exact ne_of_gt <| by
      have hplus : 0 < 1 + P.δ.1 := by linarith [P.δ.2.1]
      have hsquare : 0 < (1 + P.δ.1) ^ 2 := sq_pos_of_pos hplus
      nlinarith [sq_nonneg (x - P.γ)]
  have hgMinus_ne : gMinus x ≠ 0 := by
    dsimp [gMinus]
    exact ne_of_gt <| by
      have hminus : 0 < 1 - P.δ.1 := sub_pos.mpr P.δ.2.2
      have hsquare : 0 < (1 - P.δ.1) ^ 2 := sq_pos_of_pos hminus
      nlinarith [sq_nonneg (x - P.γ)]
  have hlogPlus :
      HasDerivAt (fun y => Real.log (gPlus y)) ((gPlus x)⁻¹ * (2 * (x - P.γ))) x := by
    simpa [gPlus] using (Real.hasDerivAt_log hgPlus_ne).comp x hgPlus
  have hlogMinus :
      HasDerivAt (fun y => Real.log (gMinus y)) ((gMinus x)⁻¹ * (2 * (x - P.γ))) x := by
    simpa [gMinus] using (Real.hasDerivAt_log hgMinus_ne).comp x hgMinus
  have hmain :
      HasDerivAt
        (fun y => (1 / 2 : ℝ) * Real.log (gPlus y) - (1 / 2 : ℝ) * Real.log (gMinus y))
        ((1 / 2 : ℝ) * ((gPlus x)⁻¹ * (2 * (x - P.γ))) -
          (1 / 2 : ℝ) * ((gMinus x)⁻¹ * (2 * (x - P.γ)))) x :=
    (hlogPlus.const_mul (1 / 2 : ℝ)).sub (hlogMinus.const_mul (1 / 2 : ℝ))
  have htarget :
      (1 / 2 : ℝ) * ((gPlus x)⁻¹ * (2 * (x - P.γ))) -
        (1 / 2 : ℝ) * ((gMinus x)⁻¹ * (2 * (x - P.γ))) =
          xi_limit_defect_potential_fourier_injective_packet_derivative P x := by
    simp [gPlus, gMinus, xi_limit_defect_potential_fourier_injective_packet_derivative,
      div_eq_mul_inv]
    ring_nf
  have hmain' :
      HasDerivAt
        (fun y => (1 / 2 : ℝ) * Real.log (gPlus y) - (1 / 2 : ℝ) * Real.log (gMinus y))
        (xi_limit_defect_potential_fourier_injective_packet_derivative P x) x := by
    rw [← htarget]
    exact hmain
  simpa [hkernel, gPlus, gMinus] using hmain'

lemma xi_limit_defect_potential_fourier_injective_potential_hasDerivAt
    (packets : List XiLimitDefectPacket) (x : ℝ) :
    HasDerivAt (xiLimitDefectPotential packets)
      (xi_limit_defect_potential_fourier_injective_potential_derivative packets x) x := by
  induction packets with
  | nil =>
      simpa [xiLimitDefectPotential,
        xi_limit_defect_potential_fourier_injective_potential_derivative] using
        (hasDerivAt_const x (c := (0 : ℝ)))
  | cons P Ps ih =>
      simpa [xiLimitDefectPotential,
        xi_limit_defect_potential_fourier_injective_potential_derivative] using
        (xi_limit_defect_potential_fourier_injective_packet_hasDerivAt P x).const_mul (P.m : ℝ) |>.add ih

lemma xi_limit_defect_potential_fourier_injective_fourier_model_eq_sum
    (packets : List XiLimitDefectPacket) (ξ : ℝ) :
    xi_limit_defect_potential_fourier_injective_fourier_model packets ξ =
      (packets.map
        (fun P => (P.m : ℂ) * xi_limit_defect_potential_fourier_injective_packet_fourier P ξ)).sum := by
  induction packets with
  | nil =>
      simp [xi_limit_defect_potential_fourier_injective_fourier_model]
  | cons P Ps ih =>
      simp [xi_limit_defect_potential_fourier_injective_fourier_model, ih]

lemma xi_limit_defect_potential_fourier_injective_nonneg
    (packets : List XiLimitDefectPacket) (x : ℝ) :
    0 ≤ xiLimitDefectPotential packets x := by
  induction packets with
  | nil =>
      simp [xiLimitDefectPotential]
  | cons P Ps ih =>
      have hm_nonneg : 0 ≤ (P.m : ℝ) := by exact_mod_cast Nat.zero_le P.m
      have hkernel_nonneg :
          0 ≤ xiPacketKernel P x :=
        xi_limit_defect_potential_fourier_injective_packet_kernel_nonneg P x
      have hhead : 0 ≤ (P.m : ℝ) * xiPacketKernel P x := mul_nonneg hm_nonneg hkernel_nonneg
      simpa [xiLimitDefectPotential] using add_nonneg hhead ih

lemma xi_limit_defect_potential_fourier_injective_positive_of_nonempty
    (P : XiLimitDefectPacket) (Ps : List XiLimitDefectPacket) (x : ℝ) (hm : 0 < P.m) :
    0 < xiLimitDefectPotential (P :: Ps) x := by
    have hm_real : 0 < (P.m : ℝ) := by exact_mod_cast hm
    have hkernel_pos :
        0 < xiPacketKernel P x :=
      xi_limit_defect_potential_fourier_injective_packet_kernel_pos P x
    have hhead : 0 < (P.m : ℝ) * xiPacketKernel P x := mul_pos hm_real hkernel_pos
    have htail : 0 ≤ xiLimitDefectPotential Ps x :=
      xi_limit_defect_potential_fourier_injective_nonneg Ps x
    simpa [xiLimitDefectPotential] using add_pos_of_pos_of_nonneg hhead htail

/-- Paper label: `thm:xi-limit-defect-potential-fourier-injective`.
For the finite packet model already used in the neighboring rationalization results, the defect
potential has an explicit derivative, its Fourier-side profile is the corresponding finite
exponential packet sum, and vanishing of the potential forces the packet list to be empty. -/
theorem paper_xi_limit_defect_potential_fourier_injective
    (packets : List XiLimitDefectPacket)
    (hm : ∀ P ∈ packets, 0 < P.m) :
    (∀ x : ℝ,
        HasDerivAt (xiLimitDefectPotential packets)
          (xi_limit_defect_potential_fourier_injective_potential_derivative packets x) x) ∧
      (∀ ξ : ℝ,
        xi_limit_defect_potential_fourier_injective_fourier_model packets ξ =
          (packets.map
            (fun P => (P.m : ℂ) * xi_limit_defect_potential_fourier_injective_packet_fourier P ξ)).sum) ∧
      ((xiLimitDefectPotential packets = fun _ => 0) ↔ packets = []) := by
  refine ⟨xi_limit_defect_potential_fourier_injective_potential_hasDerivAt packets,
    xi_limit_defect_potential_fourier_injective_fourier_model_eq_sum packets, ?_⟩
  constructor
  · intro hzero
    cases packets with
    | nil =>
        rfl
    | cons P Ps =>
        exfalso
        have hmP : 0 < P.m := hm P (by simp)
        have hvalue : xiLimitDefectPotential (P :: Ps) P.γ = 0 := by
          simpa using congrFun hzero P.γ
        have hpos :
            0 < xiLimitDefectPotential (P :: Ps) P.γ :=
          xi_limit_defect_potential_fourier_injective_positive_of_nonempty P Ps P.γ hmP
        linarith
  · intro hnil
    subst hnil
    funext x
    simp [xiLimitDefectPotential]

end Omega.Zeta
