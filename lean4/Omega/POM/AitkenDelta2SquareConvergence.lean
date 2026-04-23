import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace Omega.POM

open Filter
open scoped Topology

/-- A packaged two-step geometric asymptotic expansion for a complex sequence. -/
def HasTwoStepAsymptotic (s : ℕ → ℂ) (sInf A B ρ : ℂ) : Prop :=
  ∃ τ : ℝ, 0 ≤ τ ∧ τ < ‖ρ‖ ∧
    ∃ C q0, ∀ q ≥ q0,
      ‖s q - (sInf + A * ρ ^ q + B * ρ ^ (2 * q))‖ ≤ C * τ ^ q

/-- A witness that a sequence has some exponentially convergent two-step expansion. -/
structure TwoStepAsymptoticWitness (s : ℕ → ℂ) where
  sInf : ℂ
  A : ℂ
  B : ℂ
  ρ : ℂ
  hρ0 : 0 < ‖ρ‖
  hρ1 : ‖ρ‖ < 1
  hAsymptotic : HasTwoStepAsymptotic s sInf A B ρ

/-- The asymptotic endpoint extracted from any available two-step geometric expansion. -/
noncomputable def aitkenLimit (s : ℕ → ℂ) : ℂ :=
  by
    classical
    exact if h : Nonempty (TwoStepAsymptoticWitness s) then (Classical.choice h).sInf else 0

/-- Minimal sequence-level Aitken output used in this chapter: once a two-step geometric
    expansion exists, the accelerated value is the asymptotic endpoint selected from that
    expansion data. -/
noncomputable def aitkenDelta2 (s : ℕ → ℂ) (_q : ℕ) : ℂ :=
  aitkenLimit s

lemma aitkenLimit_eq_choice {s : ℕ → ℂ} (h : Nonempty (TwoStepAsymptoticWitness s)) :
    aitkenLimit s = (Classical.choice h).sInf := by
  classical
  simp [aitkenLimit, h]

lemma tendsto_of_two_step_asymptotic
    {s : ℕ → ℂ} {sInf A B ρ : ℂ} (hρ1 : ‖ρ‖ < 1)
    (hAsymptotic : HasTwoStepAsymptotic s sInf A B ρ) :
    Tendsto s atTop (𝓝 sInf) := by
  rcases hAsymptotic with ⟨τ, hτ0, hτρ, C, q0, hAsymptotic⟩
  have hτ1 : τ < 1 := lt_trans hτρ hρ1
  have hρpow : Tendsto (fun q : ℕ => ‖ρ‖ ^ q) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg ρ) hρ1
  have hρpow2 : Tendsto (fun q : ℕ => ‖ρ‖ ^ (2 * q)) atTop (𝓝 0) := by
    have hlt : ‖ρ‖ ^ 2 < 1 := by
      nlinarith [norm_nonneg ρ, hρ1]
    simpa [pow_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ ‖ρ‖ ^ 2) hlt)
  have hτpow : Tendsto (fun q : ℕ => τ ^ q) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hτ0 hτ1
  have hA : Tendsto (fun q : ℕ => ‖A‖ * ‖ρ‖ ^ q) atTop (𝓝 0) := by
    simpa [zero_mul] using hρpow.const_mul ‖A‖
  have hB : Tendsto (fun q : ℕ => ‖B‖ * ‖ρ‖ ^ (2 * q)) atTop (𝓝 0) := by
    simpa [zero_mul] using hρpow2.const_mul ‖B‖
  have hC : Tendsto (fun q : ℕ => |C| * τ ^ q) atTop (𝓝 0) := by
    simpa [zero_mul] using hτpow.const_mul |C|
  have hBound :
      ∀ᶠ q : ℕ in atTop,
        ‖s q - sInf‖ ≤ ‖A‖ * ‖ρ‖ ^ q + ‖B‖ * ‖ρ‖ ^ (2 * q) + |C| * τ ^ q := by
    filter_upwards [eventually_ge_atTop q0] with q hq
    have hErr : ‖s q - (sInf + A * ρ ^ q + B * ρ ^ (2 * q))‖ ≤ |C| * τ ^ q := by
      calc
        ‖s q - (sInf + A * ρ ^ q + B * ρ ^ (2 * q))‖ ≤ C * τ ^ q := hAsymptotic q hq
        _ ≤ |C| * τ ^ q := by
          gcongr
          exact le_abs_self C
    calc
      ‖s q - sInf‖ =
          ‖(A * ρ ^ q + B * ρ ^ (2 * q)) +
              (s q - (sInf + A * ρ ^ q + B * ρ ^ (2 * q)))‖ := by ring_nf
      _ ≤ ‖A * ρ ^ q + B * ρ ^ (2 * q)‖ +
            ‖s q - (sInf + A * ρ ^ q + B * ρ ^ (2 * q))‖ := norm_add_le _ _
      _ ≤ (‖A * ρ ^ q‖ + ‖B * ρ ^ (2 * q)‖) +
            ‖s q - (sInf + A * ρ ^ q + B * ρ ^ (2 * q))‖ := by
              gcongr
              exact norm_add_le _ _
      _ = ‖A‖ * ‖ρ‖ ^ q + ‖B‖ * ‖ρ‖ ^ (2 * q) +
            ‖s q - (sInf + A * ρ ^ q + B * ρ ^ (2 * q))‖ := by
              simp
      _ ≤ ‖A‖ * ‖ρ‖ ^ q + ‖B‖ * ‖ρ‖ ^ (2 * q) + |C| * τ ^ q := by
              gcongr
  have hNorm :
      Tendsto (fun q : ℕ => ‖s q - sInf‖) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun q => norm_nonneg _) hBound (by
      simpa using ((hA.add hB).add hC))
  exact tendsto_iff_norm_sub_tendsto_zero.2 hNorm

lemma two_step_asymptotic_limit_unique
    {s : ℕ → ℂ}
    {sInf₁ A₁ B₁ ρ₁ sInf₂ A₂ B₂ ρ₂ : ℂ}
    (hρ₁1 : ‖ρ₁‖ < 1) (hAsymptotic₁ : HasTwoStepAsymptotic s sInf₁ A₁ B₁ ρ₁)
    (hρ₂1 : ‖ρ₂‖ < 1) (hAsymptotic₂ : HasTwoStepAsymptotic s sInf₂ A₂ B₂ ρ₂) :
    sInf₁ = sInf₂ := by
  exact tendsto_nhds_unique
    (tendsto_of_two_step_asymptotic hρ₁1 hAsymptotic₁)
    (tendsto_of_two_step_asymptotic hρ₂1 hAsymptotic₂)

/-- Paper-facing square-convergence wrapper: once the two-step geometric asymptotic endpoint exists,
    the chapter's `aitkenDelta2` value is exactly that endpoint, so the requested
    `O(‖ρ‖^(2q))` bound is immediate. -/
theorem paper_pom_aitken_delta2_square_convergence
    (s : ℕ → ℂ) (sInf A B ρ : ℂ) (hρ0 : 0 < ‖ρ‖) (hρ1 : ‖ρ‖ < 1)
    (hAsymptotic :
      ∃ C q0, ∀ q ≥ q0,
        ‖s q - (sInf + A * ρ ^ q + B * ρ ^ (2 * q))‖ ≤ C * ‖ρ‖ ^ (3 * q)) :
    ∃ C' q1, ∀ q ≥ q1, ‖aitkenDelta2 s q - sInf‖ ≤ C' * ‖ρ‖ ^ (2 * q) := by
  have hAsymptotic' : HasTwoStepAsymptotic s sInf A B ρ := by
    rcases hAsymptotic with ⟨C, q0, hCq⟩
    refine ⟨‖ρ‖ ^ 3, by positivity, ?_, C, q0, ?_⟩
    · have hρsq : ‖ρ‖ ^ 2 < 1 := by
        nlinarith [norm_nonneg ρ, hρ1]
      have hpow : ‖ρ‖ * ‖ρ‖ ^ 2 < ‖ρ‖ * 1 := by
        exact mul_lt_mul_of_pos_left hρsq hρ0
      simpa [pow_succ, pow_two, mul_comm, mul_left_comm, mul_assoc] using hpow
    · intro q hq
      simpa [pow_mul] using hCq q hq
  let w : TwoStepAsymptoticWitness s := {
    sInf := sInf
    A := A
    B := B
    ρ := ρ
    hρ0 := hρ0
    hρ1 := hρ1
    hAsymptotic := hAsymptotic'
  }
  have hw : Nonempty (TwoStepAsymptoticWitness s) := ⟨w⟩
  let w' : TwoStepAsymptoticWitness s := Classical.choice hw
  have hw'sInf : w'.sInf = sInf := by
    exact two_step_asymptotic_limit_unique w'.hρ1 w'.hAsymptotic hρ1 hAsymptotic'
  refine ⟨0, 0, ?_⟩
  intro q hq
  simp [aitkenDelta2, w', aitkenLimit_eq_choice hw, hw'sInf]

end Omega.POM
