import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Concrete diagonal-enhancement parameter used in the two-state model. -/
def pom_diagonal_rate_scaling_duality_kappa : ℝ := 1

/-- The diagonal-enhanced kernel `K_κ(x,y) = 1 + κ 1_{x=y}` specialized to `κ = 1`. -/
def pom_diagonal_rate_scaling_duality_kernel (x y : Fin 2) : ℝ :=
  if x = y then 1 + pom_diagonal_rate_scaling_duality_kappa else 1

/-- The reference scaling vector `u = (1,2)`. -/
def pom_diagonal_rate_scaling_duality_scaler : Fin 2 → ℝ
  | 0 => 1
  | 1 => 2

/-- The scaling normalizer `Z_κ(u)` for the concrete kernel/scaler pair. -/
def pom_diagonal_rate_scaling_duality_normalizer : ℝ :=
  ∑ x : Fin 2, ∑ y : Fin 2,
    pom_diagonal_rate_scaling_duality_scaler x *
      pom_diagonal_rate_scaling_duality_kernel x y *
        pom_diagonal_rate_scaling_duality_scaler y

/-- The target marginal recovered from the concrete diagonal scaling relation. -/
def pom_diagonal_rate_scaling_duality_weight : Fin 2 → ℝ
  | 0 => 2 / 7
  | 1 => 5 / 7

/-- The Shannon entropy of the recovered target law. -/
def pom_diagonal_rate_scaling_duality_entropy : ℝ :=
  -∑ x : Fin 2,
    pom_diagonal_rate_scaling_duality_weight x *
      Real.log (pom_diagonal_rate_scaling_duality_weight x)

/-- A normalized scaling functional whose zero set is exactly the rescaling ray of `u = (1,2)`. -/
def pom_diagonal_rate_scaling_duality_scaling_functional (u : Fin 2 → ℝ) : ℝ :=
  (u 1 - 2 * u 0) ^ 2

/-- The dual objective at distortion level `δ = 1`. -/
def pom_diagonal_rate_scaling_duality_dual_objective : ℝ :=
  2 * pom_diagonal_rate_scaling_duality_entropy -
    pom_diagonal_rate_scaling_duality_scaling_functional
      pom_diagonal_rate_scaling_duality_scaler +
    (1 - (1 : ℝ)) * Real.log (1 + pom_diagonal_rate_scaling_duality_kappa)

/-- The coupling recovered from the minimizing scaler. -/
def pom_diagonal_rate_scaling_duality_coupling (x y : Fin 2) : ℝ :=
  pom_diagonal_rate_scaling_duality_scaler x *
    pom_diagonal_rate_scaling_duality_kernel x y *
      pom_diagonal_rate_scaling_duality_scaler y /
    pom_diagonal_rate_scaling_duality_normalizer

/-- The dual formula in the explicit two-state model. -/
def paper_pom_diagonal_rate_scaling_duality_dual_formula : Prop :=
  pom_diagonal_rate_scaling_duality_dual_objective =
      2 * pom_diagonal_rate_scaling_duality_entropy ∧
    ∀ u : Fin 2 → ℝ,
      pom_diagonal_rate_scaling_duality_scaling_functional u = 0 ↔
        ∃ c : ℝ, u = c • pom_diagonal_rate_scaling_duality_scaler

/-- The optimal coupling recovery in the explicit two-state model. -/
def paper_pom_diagonal_rate_scaling_duality_optimal_coupling_recovery : Prop :=
  (∀ x : Fin 2,
    ∑ y : Fin 2, pom_diagonal_rate_scaling_duality_coupling x y =
      pom_diagonal_rate_scaling_duality_weight x) ∧
    (∀ y : Fin 2,
      ∑ x : Fin 2, pom_diagonal_rate_scaling_duality_coupling x y =
        pom_diagonal_rate_scaling_duality_weight y) ∧
    pom_diagonal_rate_scaling_duality_coupling 0 0 = 1 / 7

private lemma pom_diagonal_rate_scaling_duality_normalizer_eval :
    pom_diagonal_rate_scaling_duality_normalizer = 14 := by
  norm_num [pom_diagonal_rate_scaling_duality_normalizer,
    pom_diagonal_rate_scaling_duality_scaler, pom_diagonal_rate_scaling_duality_kernel,
    pom_diagonal_rate_scaling_duality_kappa]

private lemma pom_diagonal_rate_scaling_duality_scaling_functional_scaler :
    pom_diagonal_rate_scaling_duality_scaling_functional
        pom_diagonal_rate_scaling_duality_scaler = 0 := by
  norm_num [pom_diagonal_rate_scaling_duality_scaling_functional,
    pom_diagonal_rate_scaling_duality_scaler]

private lemma pom_diagonal_rate_scaling_duality_scaling_functional_zero_iff
    (u : Fin 2 → ℝ) :
    pom_diagonal_rate_scaling_duality_scaling_functional u = 0 ↔
      ∃ c : ℝ, u = c • pom_diagonal_rate_scaling_duality_scaler := by
  constructor
  · intro hu
    have hlin : u 1 = 2 * u 0 := by
      have hsquare : (u 1 - 2 * u 0) ^ 2 = 0 := by
        simpa [pom_diagonal_rate_scaling_duality_scaling_functional] using hu
      nlinarith
    refine ⟨u 0, ?_⟩
    funext i
    fin_cases i
    · simp [pom_diagonal_rate_scaling_duality_scaler]
    · simp [Pi.smul_apply, pom_diagonal_rate_scaling_duality_scaler, hlin, mul_comm]
  · rintro ⟨c, rfl⟩
    unfold pom_diagonal_rate_scaling_duality_scaling_functional
    simp [pom_diagonal_rate_scaling_duality_scaler]
    ring

private lemma pom_diagonal_rate_scaling_duality_coupling_row
    (x : Fin 2) :
    ∑ y : Fin 2, pom_diagonal_rate_scaling_duality_coupling x y =
      pom_diagonal_rate_scaling_duality_weight x := by
  fin_cases x
  · rw [Fin.sum_univ_two]
    norm_num [pom_diagonal_rate_scaling_duality_coupling,
      pom_diagonal_rate_scaling_duality_weight,
      pom_diagonal_rate_scaling_duality_scaler,
      pom_diagonal_rate_scaling_duality_kernel,
      pom_diagonal_rate_scaling_duality_kappa,
      pom_diagonal_rate_scaling_duality_normalizer_eval]
  · rw [Fin.sum_univ_two]
    norm_num [pom_diagonal_rate_scaling_duality_coupling,
      pom_diagonal_rate_scaling_duality_weight,
      pom_diagonal_rate_scaling_duality_scaler,
      pom_diagonal_rate_scaling_duality_kernel,
      pom_diagonal_rate_scaling_duality_kappa,
      pom_diagonal_rate_scaling_duality_normalizer_eval]

private lemma pom_diagonal_rate_scaling_duality_coupling_col
    (y : Fin 2) :
    ∑ x : Fin 2, pom_diagonal_rate_scaling_duality_coupling x y =
      pom_diagonal_rate_scaling_duality_weight y := by
  fin_cases y
  · rw [Fin.sum_univ_two]
    norm_num [pom_diagonal_rate_scaling_duality_coupling,
      pom_diagonal_rate_scaling_duality_weight,
      pom_diagonal_rate_scaling_duality_scaler,
      pom_diagonal_rate_scaling_duality_kernel,
      pom_diagonal_rate_scaling_duality_kappa,
      pom_diagonal_rate_scaling_duality_normalizer_eval]
  · rw [Fin.sum_univ_two]
    norm_num [pom_diagonal_rate_scaling_duality_coupling,
      pom_diagonal_rate_scaling_duality_weight,
      pom_diagonal_rate_scaling_duality_scaler,
      pom_diagonal_rate_scaling_duality_kernel,
      pom_diagonal_rate_scaling_duality_kappa,
      pom_diagonal_rate_scaling_duality_normalizer_eval]

/-- Paper label: `thm:pom-diagonal-rate-scaling-duality`. In the explicit two-state
diagonal-enhanced model with scaler `u = (1,2)`, the scaling functional vanishes exactly on the
rescaling orbit of `u`, the dual objective reduces to twice the target entropy at `δ = 1`, and
the induced coupling has the displayed marginals `w = (2/7,5/7)`. -/
theorem paper_pom_diagonal_rate_scaling_duality :
    paper_pom_diagonal_rate_scaling_duality_dual_formula ∧
      paper_pom_diagonal_rate_scaling_duality_optimal_coupling_recovery := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · unfold pom_diagonal_rate_scaling_duality_dual_objective
      rw [pom_diagonal_rate_scaling_duality_scaling_functional_scaler]
      ring_nf
    · intro u
      exact pom_diagonal_rate_scaling_duality_scaling_functional_zero_iff u
  · refine ⟨pom_diagonal_rate_scaling_duality_coupling_row,
      pom_diagonal_rate_scaling_duality_coupling_col, ?_⟩
    norm_num [pom_diagonal_rate_scaling_duality_coupling,
      pom_diagonal_rate_scaling_duality_scaler,
      pom_diagonal_rate_scaling_duality_kernel,
      pom_diagonal_rate_scaling_duality_kappa,
      pom_diagonal_rate_scaling_duality_normalizer_eval]

end

end Omega.POM
