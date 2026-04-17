import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Exact affine local model with slope `m` and zero at `γ`. -/
def rsGabckeExact (m γ : ℝ) : ℝ → ℝ :=
  fun t => m * (t - γ)

/-- Truncated affine local model with constant remainder `e`. -/
def rsGabckeApprox (m γ e : ℝ) : ℝ → ℝ :=
  fun t => rsGabckeExact m γ t + e

/-- The unique zero of the affine approximation. -/
noncomputable def rsGabckeApproxZero (γ m e : ℝ) : ℝ :=
  γ - e / m

/-- Inter-level difference between two affine truncations. -/
def rsGabckeDelta (eK eK1 : ℝ) : ℝ → ℝ :=
  fun _ => eK1 - eK

/-- Paper-facing affine certificate for the local-zero stability pattern: endpoint signs are
preserved under a bounded remainder, the approximate zero stays inside the certified interval,
the affine approximation has a unique zero there, and the inter-level step is controlled by the
difference term.
    thm:cdim-rs-gabcke-local-zero-stability -/
theorem paper_cdim_rs_gabcke_local_zero_stability
    (γ ρ m eK eK1 : ℝ)
    (hρ : 0 < ρ) (hm : 0 < m)
    (heK : |eK| ≤ m * ρ) (heK1 : |eK1| ≤ m * ρ) :
    let I := Set.Icc (γ - ρ) (γ + ρ)
    let Z := rsGabckeExact m γ
    let ZK := rsGabckeApprox m γ eK
    let ZK1 := rsGabckeApprox m γ eK1
    let γK := rsGabckeApproxZero γ m eK
    let γK1 := rsGabckeApproxZero γ m eK1
    let Δ := rsGabckeDelta eK eK1
    Z γ = 0 ∧
      ZK (γ - ρ) ≤ 0 ∧
      0 ≤ ZK (γ + ρ) ∧
      γ - ρ ≤ γK ∧
      γK ≤ γ + ρ ∧
      ZK γK = 0 ∧
      (∀ t : ℝ, ZK t = 0 → t = γK) ∧
      |γK - γ| ≤ |eK| / m ∧
      γ - ρ ≤ γK1 ∧
      γK1 ≤ γ + ρ ∧
      ZK1 γK1 = 0 ∧
      γK1 - γK = -(Δ γK) / m ∧
      |γK1 - γK| ≤ |Δ γK| / m := by
  dsimp [rsGabckeExact, rsGabckeApprox, rsGabckeApproxZero, rsGabckeDelta]
  have hmne : m ≠ 0 := hm.ne'
  have hK_upper : eK ≤ m * ρ := le_trans (le_abs_self eK) heK
  have hK_lower : -(m * ρ) ≤ eK := by
    have : -|eK| ≤ eK := neg_abs_le eK
    exact le_trans (by simpa using (neg_le_neg heK)) this
  have hK1_upper : eK1 ≤ m * ρ := le_trans (le_abs_self eK1) heK1
  have hK1_lower : -(m * ρ) ≤ eK1 := by
    have : -|eK1| ≤ eK1 := neg_abs_le eK1
    exact le_trans (by simpa using (neg_le_neg heK1)) this
  have hsubK : γ - eK / m - γ = -(eK / m) := by ring
  have hsubK1 : γ - eK1 / m - γ = -(eK1 / m) := by ring
  have hlocK_abs : |(γ - eK / m) - γ| ≤ ρ := by
    rw [hsubK, abs_neg, abs_div, abs_of_pos hm]
    have hdiv : |eK| / m ≤ ρ := by
      rw [_root_.div_le_iff₀ hm]
      simpa [mul_comm] using heK
    simpa using hdiv
  have hlocK1_abs : |(γ - eK1 / m) - γ| ≤ ρ := by
    rw [hsubK1, abs_neg, abs_div, abs_of_pos hm]
    have hdiv : |eK1| / m ≤ ρ := by
      rw [_root_.div_le_iff₀ hm]
      simpa [mul_comm] using heK1
    simpa using hdiv
  have hrootK : rsGabckeApprox m γ eK (γ - eK / m) = 0 := by
    unfold rsGabckeApprox rsGabckeExact
    field_simp [hmne]
    ring
  have hrootK1 : rsGabckeApprox m γ eK1 (γ - eK1 / m) = 0 := by
    unfold rsGabckeApprox rsGabckeExact
    field_simp [hmne]
    ring
  have huniqK : ∀ t : ℝ, rsGabckeApprox m γ eK t = 0 → t = γ - eK / m := by
    intro t ht
    unfold rsGabckeApprox rsGabckeExact at ht
    change t = γ - eK / m
    field_simp [hmne] at ht ⊢
    linarith
  have hstepEq : (γ - eK1 / m) - (γ - eK / m) = -(eK1 - eK) / m := by
    field_simp [hmne]
    ring
  refine ⟨by simp, ?_, ?_, ?_, ?_, hrootK, huniqK, ?_, ?_, ?_, hrootK1, hstepEq, ?_⟩
  · linarith
  · linarith
  · have hloc := abs_le.mp hlocK_abs
    linarith
  · have hloc := abs_le.mp hlocK_abs
    linarith
  · have hEq : |(γ - eK / m) - γ| = |eK| / m := by
      rw [hsubK, abs_neg, abs_div, abs_of_pos hm]
    rw [hEq]
  · have hloc := abs_le.mp hlocK1_abs
    linarith
  · have hloc := abs_le.mp hlocK1_abs
    linarith
  · have hEq : |(γ - eK1 / m) - (γ - eK / m)| = |eK1 - eK| / m := by
      calc
        |(γ - eK1 / m) - (γ - eK / m)| = |-(eK1 - eK) / m| := by rw [hstepEq]
        _ = |eK1 - eK| / m := by rw [abs_div, abs_neg, abs_of_pos hm]
    exact hEq.le

end Omega.CircleDimension
