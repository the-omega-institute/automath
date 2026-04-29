import Mathlib.Tactic
import Omega.Zeta.XiToeplitzDetVerblunsky

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

namespace XiToeplitzDetVerblunskyData

/-- The cumulative product of the principal Toeplitz determinants. This renormalized sequence has
the feature that its discrete curvature recovers the one-step Schur factor. -/
def cumulativePrincipalMinor (D : XiToeplitzDetVerblunskyData) : ℕ → ℝ
  | 0 => 1
  | n + 1 => D.cumulativePrincipalMinor n * D.toeplitzDet n

/-- The discrete curvature of the cumulative principal-minor sequence. -/
def discreteCurvature (D : XiToeplitzDetVerblunskyData) (m : ℕ) : ℝ :=
  D.cumulativePrincipalMinor (m + 2) * D.cumulativePrincipalMinor m /
    D.cumulativePrincipalMinor (m + 1) ^ 2

/-- The modulus recovered from the discrete curvature. -/
def recoveredModulus (D : XiToeplitzDetVerblunskyData) (m : ℕ) : ℝ :=
  Real.sqrt (1 - D.discreteCurvature m)

lemma cumulativePrincipalMinor_succ (D : XiToeplitzDetVerblunskyData) (n : ℕ) :
    D.cumulativePrincipalMinor (n + 1) = D.cumulativePrincipalMinor n * D.toeplitzDet n := by
  simp [cumulativePrincipalMinor]

lemma toeplitzDet_pos_of_good (D : XiToeplitzDetVerblunskyData)
    (hgood : ∀ j < D.steps, |D.alphaAt j| < 1) {m : ℕ} (hm : m ≤ D.steps) :
    0 < D.toeplitzDet m := by
  apply D.toeplitzDet_pos_of_prefix_good
  intro j hj
  exact hgood j (lt_of_lt_of_le hj hm)

lemma cumulativePrincipalMinor_pos (D : XiToeplitzDetVerblunskyData)
    (hgood : ∀ j < D.steps, |D.alphaAt j| < 1) :
    ∀ {n : ℕ}, n ≤ D.steps + 1 → 0 < D.cumulativePrincipalMinor n
  | 0, _ => by simp [cumulativePrincipalMinor]
  | n + 1, hn => by
      have hprev : n ≤ D.steps + 1 := by omega
      have hdet : n ≤ D.steps := by omega
      have hcum : 0 < D.cumulativePrincipalMinor n := D.cumulativePrincipalMinor_pos hgood hprev
      have htoeplitz : 0 < D.toeplitzDet n := D.toeplitzDet_pos_of_good hgood hdet
      simpa [cumulativePrincipalMinor] using mul_pos hcum htoeplitz

lemma discreteCurvature_eq_stepFactor (D : XiToeplitzDetVerblunskyData)
    (hgood : ∀ j < D.steps, |D.alphaAt j| < 1) {m : ℕ} (hm : m < D.steps) :
    D.discreteCurvature m = D.stepFactor m := by
  have hcum_m : 0 < D.cumulativePrincipalMinor m :=
    D.cumulativePrincipalMinor_pos hgood (by omega)
  have hdet_m : 0 < D.toeplitzDet m := D.toeplitzDet_pos_of_good hgood (Nat.le_of_lt hm)
  have hcum_m_ne : D.cumulativePrincipalMinor m ≠ 0 := ne_of_gt hcum_m
  have hdet_m_ne : D.toeplitzDet m ≠ 0 := ne_of_gt hdet_m
  calc
    D.discreteCurvature m
        = D.toeplitzDet (m + 1) / D.toeplitzDet m := by
            unfold discreteCurvature
            rw [D.cumulativePrincipalMinor_succ (m + 1), D.cumulativePrincipalMinor_succ m]
            field_simp [hcum_m_ne, hdet_m_ne]
    _ = D.stepFactor m := by
          apply (div_eq_iff hdet_m_ne).2
          simp [XiToeplitzDetVerblunskyData.toeplitzDet]
          ring

lemma discreteCurvature_eq_one_sub_abs_sq (D : XiToeplitzDetVerblunskyData)
    (hgood : ∀ j < D.steps, |D.alphaAt j| < 1) {m : ℕ} (hm : m < D.steps) :
    D.discreteCurvature m = 1 - |D.alphaAt m| ^ 2 := by
  rw [D.discreteCurvature_eq_stepFactor hgood hm, XiToeplitzDetVerblunskyData.stepFactor]
  congr 1
  rw [sq_abs]

lemma recoveredModulus_eq_abs_alphaAt (D : XiToeplitzDetVerblunskyData)
    (hgood : ∀ j < D.steps, |D.alphaAt j| < 1) {m : ℕ} (hm : m < D.steps) :
    D.recoveredModulus m = |D.alphaAt m| := by
  unfold recoveredModulus
  rw [D.discreteCurvature_eq_one_sub_abs_sq hgood hm]
  have hsquare : 1 - (1 - |D.alphaAt m| ^ 2) = (|D.alphaAt m|) ^ 2 := by ring
  rw [hsquare]
  simpa using (Real.sqrt_sq_eq_abs (|D.alphaAt m|))

end XiToeplitzDetVerblunskyData

open XiToeplitzDetVerblunskyData

/-- Paper label: `thm:xi-toeplitz-principal-minor-discrete-curvature-recovery`.
For a finite Toeplitz determinant recursion with all Verblunsky moduli below `1`, the discrete
curvature of the cumulative principal-minor sequence is exactly `1 - |α_m|²`; therefore the
Verblunsky modulus sequence is recovered uniquely from those principal-minor ratios. -/
theorem paper_xi_toeplitz_principal_minor_discrete_curvature_recovery
    (D : XiToeplitzDetVerblunskyData)
    (hgood : ∀ m < D.steps, |D.alphaAt m| < 1) :
    (∀ m < D.steps, D.discreteCurvature m = 1 - |D.alphaAt m| ^ 2) ∧
      (∀ m < D.steps, D.recoveredModulus m = |D.alphaAt m|) ∧
      (∀ β : ℕ → ℝ,
        (∀ m < D.steps, D.discreteCurvature m = 1 - |β m| ^ 2) →
          ∀ m < D.steps, |β m| = |D.alphaAt m|) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    exact D.discreteCurvature_eq_one_sub_abs_sq hgood hm
  · intro m hm
    exact D.recoveredModulus_eq_abs_alphaAt hgood hm
  · intro β hβ m hm
    have hα : D.discreteCurvature m = 1 - |D.alphaAt m| ^ 2 :=
      D.discreteCurvature_eq_one_sub_abs_sq hgood hm
    have hβm : D.discreteCurvature m = 1 - |β m| ^ 2 := hβ m hm
    have habs_sq : |β m| ^ 2 = |D.alphaAt m| ^ 2 := by nlinarith [hα, hβm]
    have hβ_nonneg : 0 ≤ |β m| := abs_nonneg _
    have hα_nonneg : 0 ≤ |D.alphaAt m| := abs_nonneg _
    nlinarith

end

end Omega.Zeta
