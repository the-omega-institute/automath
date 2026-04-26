import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite Jacobi-certificate data together with spectral endpoints and global
Gershgorin row guards. -/
structure xi_jacobi_gershgorin_support_guardrail_data where
  κ : ℕ
  hκ : 0 < κ
  beta : Fin κ → ℝ
  alphaPrev : Fin κ → ℝ
  alphaNext : Fin κ → ℝ
  lowerGuard : ℝ
  upperGuard : ℝ
  atom : Fin κ → ℝ
  aMin : ℝ
  aMax : ℝ
  deltaMin : ℝ
  deltaMax : ℝ
  hlowerGuard : ∀ i, lowerGuard ≤ beta i - alphaPrev i - alphaNext i
  hupperGuard : ∀ i, beta i + alphaPrev i + alphaNext i ≤ upperGuard
  hgershgorin : ∀ j, ∃ i, beta i - alphaPrev i - alphaNext i ≤ atom j ∧
    atom j ≤ beta i + alphaPrev i + alphaNext i
  haMin_le : ∀ j, aMin ≤ atom j
  haMin_eq : ∃ j, atom j = aMin
  haMax_ge : ∀ j, atom j ≤ aMax
  haMax_eq : ∃ j, atom j = aMax
  hdeltaMin : deltaMin = aMin - 1
  hdeltaMax : deltaMax = aMax - 1

namespace xi_jacobi_gershgorin_support_guardrail_data

def rowLower (D : xi_jacobi_gershgorin_support_guardrail_data) (i : Fin D.κ) : ℝ :=
  D.beta i - D.alphaPrev i - D.alphaNext i

def rowUpper (D : xi_jacobi_gershgorin_support_guardrail_data) (i : Fin D.κ) : ℝ :=
  D.beta i + D.alphaPrev i + D.alphaNext i

def support_guardrail (D : xi_jacobi_gershgorin_support_guardrail_data) : Prop :=
  D.lowerGuard ≤ D.aMin ∧
    D.aMin ≤ D.aMax ∧
    D.aMax ≤ D.upperGuard ∧
    D.deltaMin ∈ Set.Icc (D.lowerGuard - 1) (D.upperGuard - 1) ∧
    D.deltaMax ∈ Set.Icc (D.lowerGuard - 1) (D.upperGuard - 1)

end xi_jacobi_gershgorin_support_guardrail_data

open xi_jacobi_gershgorin_support_guardrail_data

/-- Paper label: `prop:xi-jacobi-gershgorin-support-guardrail`. -/
theorem paper_xi_jacobi_gershgorin_support_guardrail
    (D : xi_jacobi_gershgorin_support_guardrail_data) : D.support_guardrail := by
  rcases D.haMin_eq with ⟨jmin, hjmin⟩
  rcases D.hgershgorin jmin with ⟨imin, hrowmin, _⟩
  have hlower : D.lowerGuard ≤ D.aMin := by
    calc
      D.lowerGuard ≤ D.rowLower imin := by
        simpa [rowLower] using D.hlowerGuard imin
      _ ≤ D.atom jmin := by
        simpa [rowLower] using hrowmin
      _ = D.aMin := hjmin
  rcases D.haMax_eq with ⟨jmax, hjmax⟩
  rcases D.hgershgorin jmax with ⟨imax, _, hrowmax⟩
  have hupper : D.aMax ≤ D.upperGuard := by
    calc
      D.aMax = D.atom jmax := hjmax.symm
      _ ≤ D.rowUpper imax := by
        simpa [rowUpper] using hrowmax
      _ ≤ D.upperGuard := by
        simpa [rowUpper] using D.hupperGuard imax
  have hamin_le_amax : D.aMin ≤ D.aMax := by
    calc
      D.aMin ≤ D.atom jmax := D.haMin_le jmax
      _ = D.aMax := hjmax
  have hdeltaMin_bounds : D.deltaMin ∈ Set.Icc (D.lowerGuard - 1) (D.upperGuard - 1) := by
    rw [Set.mem_Icc, D.hdeltaMin]
    constructor <;> linarith
  have hdeltaMax_bounds : D.deltaMax ∈ Set.Icc (D.lowerGuard - 1) (D.upperGuard - 1) := by
    rw [Set.mem_Icc, D.hdeltaMax]
    constructor <;> linarith
  exact ⟨hlower, hamin_le_amax, hupper, hdeltaMin_bounds, hdeltaMax_bounds⟩

end Omega.Zeta
