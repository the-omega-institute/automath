import Omega.EA.KernelChebotarevExp
import Omega.EA.KernelWeightedPrimeOrbit
import Mathlib.Tactic

namespace Omega.EA

/-- Concrete data for the kernel RH/GRH square-root error wrapper. -/
structure KernelRHSqrtErrorData (G : Type*) where
  instFintype : Fintype G
  B : Nat → G → Real
  lambda1 : Real
  Lambda : Real

/-- Kernel RH/GRH converts an exponential error with rate `Lambda` into the square-root scale
once `Lambda ≤ sqrt(lambda1)` and `Lambda` is nonnegative. -/
def KernelRHSqrtError {G : Type*} (D : KernelRHSqrtErrorData G) : Prop := by
  let _ := D.instFintype
  exact
    (∀ c, ∃ C : Real, ∀ n,
      |D.B n c - (1 / (Fintype.card G : Real)) * D.lambda1 ^ n| ≤ C * D.Lambda ^ n) →
    0 ≤ D.Lambda →
    D.Lambda ≤ Real.sqrt D.lambda1 →
    ∀ c, ∃ C : Real, ∀ n,
      |D.B n c - (1 / (Fintype.card G : Real)) * D.lambda1 ^ n| ≤
        C * (Real.sqrt D.lambda1) ^ n

/-- Paper label: `cor:kernel-rh-sqrt-error`. -/
theorem paper_kernel_rh_sqrt_error {G : Type*} (D : KernelRHSqrtErrorData G) :
    KernelRHSqrtError D := by
  let _ := D.instFintype
  intro hChebotarev hLambdaNonneg hSqrtGap
  let traceFormula : Prop :=
    ∀ c, ∃ C : Real, ∀ n,
      |D.B n c - (1 / (Fintype.card G : Real)) * D.lambda1 ^ n| ≤ C * D.Lambda ^ n
  let spectralGapControl : Prop :=
    0 ≤ D.Lambda ∧ D.Lambda ≤ Real.sqrt D.lambda1
  let weightedPrimeOrbitAsymptotic : Prop :=
    ∀ c, ∃ C : Real, ∀ n,
      |D.B n c - (1 / (Fintype.card G : Real)) * D.lambda1 ^ n| ≤
        C * (Real.sqrt D.lambda1) ^ n
  have hPack :
      traceFormula ∧ spectralGapControl ∧ weightedPrimeOrbitAsymptotic := by
    apply
      paper_kernel_weighted_prime_orbit traceFormula spectralGapControl
        weightedPrimeOrbitAsymptotic
    · simpa [traceFormula] using hChebotarev
    · exact ⟨hLambdaNonneg, hSqrtGap⟩
    · intro hTrace hGap
      rcases hGap with ⟨hLambdaNonneg', hSqrtGap'⟩
      intro c
      rcases paper_kernel_chebotarev_exp D.B D.lambda1 D.Lambda hTrace c with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      intro n
      have hBase : D.Lambda ^ n ≤ (Real.sqrt D.lambda1) ^ n := by
        exact pow_le_pow_left₀ hLambdaNonneg' hSqrtGap' n
      have hC_nonneg : 0 ≤ C := by
        have h0 := hC 0
        have hAbsNonneg : 0 ≤
            |D.B 0 c - (1 / (Fintype.card G : Real)) * D.lambda1 ^ (0 : ℕ)| := by
          exact abs_nonneg _
        have hMulNonneg : 0 ≤ C * D.Lambda ^ (0 : ℕ) := le_trans hAbsNonneg h0
        simpa using hMulNonneg
      exact le_trans (hC n) (by gcongr)
  simpa [weightedPrimeOrbitAsymptotic] using hPack.2.2
