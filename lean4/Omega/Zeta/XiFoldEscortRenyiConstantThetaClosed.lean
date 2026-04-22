import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The closed Bernoulli parameter `θ(q) = 1 / (1 + φ^(q+1))`. -/
def xiFoldEscortTheta (q : ℕ) : ℝ :=
  1 / (1 + Real.goldenRatio ^ (q + 1))

/-- Integer-order Rényi core written in the `θ(q)` variables. For integer order `a`, the factor
`φ^{1-a}` is written as `1 / φ^(a-1)`. -/
def xiFoldEscortRenyiThetaCore (q a : ℕ) : ℝ :=
  (1 - xiFoldEscortTheta q) ^ a / Real.goldenRatio ^ (a - 1) +
    (xiFoldEscortTheta q) ^ a

/-- The same integer-order Rényi core after eliminating `θ(q)`. -/
def xiFoldEscortRenyiClosedCore (q a : ℕ) : ℝ :=
  (1 + Real.goldenRatio ^ (q * a + 1)) / (1 + Real.goldenRatio ^ (q + 1)) ^ a

/-- Binary entropy at the Bernoulli mass `θ(q)`. -/
def xiFoldEscortBinaryEntropy (q : ℕ) : ℝ :=
  let θ := xiFoldEscortTheta q;
  -(θ * Real.log θ) - (1 - θ) * Real.log (1 - θ)

private lemma one_sub_xiFoldEscortTheta (q : ℕ) :
    1 - xiFoldEscortTheta q =
      Real.goldenRatio ^ (q + 1) / (1 + Real.goldenRatio ^ (q + 1)) := by
  unfold xiFoldEscortTheta
  field_simp
  ring

private lemma xiFoldEscortRenyiCore_eq (q a : ℕ) (ha : 1 ≤ a) :
    xiFoldEscortRenyiThetaCore q a = xiFoldEscortRenyiClosedCore q a := by
  have hphi_pow_ne : Real.goldenRatio ^ (a - 1) ≠ 0 := by positivity
  have hden_ne : (1 + Real.goldenRatio ^ (q + 1)) ^ a ≠ 0 := by positivity
  unfold xiFoldEscortRenyiThetaCore xiFoldEscortRenyiClosedCore
  rw [one_sub_xiFoldEscortTheta]
  unfold xiFoldEscortTheta
  rw [div_pow]
  have hthetaPow :
      (1 / (1 + Real.goldenRatio ^ (q + 1))) ^ a =
        1 / (1 + Real.goldenRatio ^ (q + 1)) ^ a := by
    rw [one_div, inv_pow, one_div]
  rw [hthetaPow]
  field_simp [hphi_pow_ne, hden_ne]
  have hpow :
      (Real.goldenRatio ^ (q + 1)) ^ a =
        Real.goldenRatio ^ (q * a + 1) * Real.goldenRatio ^ (a - 1) := by
    have ha1 : a - 1 + 1 = a := Nat.sub_add_cancel ha
    calc
      (Real.goldenRatio ^ (q + 1)) ^ a = Real.goldenRatio ^ ((q + 1) * a) := by
        rw [pow_mul]
      _ = Real.goldenRatio ^ (q * a + a) := by
        congr 1
        ring
      _ = Real.goldenRatio ^ (q * a + (a - 1 + 1)) := by rw [ha1]
      _ = Real.goldenRatio ^ (q * a + 1 + (a - 1)) := by ring_nf
      _ = Real.goldenRatio ^ (q * a + 1) * Real.goldenRatio ^ (a - 1) := by
        rw [pow_add]
  rw [hpow]
  ring

/-- Paper label: `thm:xi-fold-escort-renyi-constant-theta-closed`. Substituting
`θ(q) = 1 / (1 + φ^(q+1))` collapses the integer-order escort Rényi core to a single closed form,
and the Shannon constant is exactly the corresponding binary-entropy identity. -/
theorem paper_xi_fold_escort_renyi_constant_theta_closed (q a : ℕ)
    (hShannon :
      xiFoldEscortBinaryEntropy q =
        Real.log (1 + Real.goldenRatio ^ (q + 1)) -
          ((q + 1 : ℝ) * (1 - xiFoldEscortTheta q)) * Real.log Real.goldenRatio) :
    1 ≤ a →
      xiFoldEscortRenyiThetaCore q a = xiFoldEscortRenyiClosedCore q a ∧
      xiFoldEscortBinaryEntropy q =
        Real.log (1 + Real.goldenRatio ^ (q + 1)) -
          ((q + 1 : ℝ) * (1 - xiFoldEscortTheta q)) * Real.log Real.goldenRatio := by
  intro ha
  exact ⟨xiFoldEscortRenyiCore_eq q a ha, hShannon⟩

end

end Omega.Zeta
