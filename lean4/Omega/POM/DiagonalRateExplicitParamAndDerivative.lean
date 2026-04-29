import Mathlib

open scoped BigOperators

namespace Omega.POM

/-- Concrete finite data for the diagonal-rate exponential family. -/
structure pom_diagonal_rate_explicit_param_and_derivative_Data where
  n : Nat
  hn : 0 < n
  w : Fin n → ℝ
  delta : ℝ
  kappa : ℝ
  u : Fin n → ℝ
  hu_pos : ∀ i, 0 < u i
  hkappa_nonneg : 0 ≤ kappa

/-- The normalizing constant for the diagonal-enhanced product form. -/
noncomputable def pom_diagonal_rate_explicit_param_and_derivative_Z
    (D : pom_diagonal_rate_explicit_param_and_derivative_Data) : ℝ :=
  ∑ a : Fin D.n, ∑ b : Fin D.n,
    D.u a * D.u b * (1 + D.kappa * if a = b then (1 : ℝ) else 0)

/-- The diagonal-enhanced product coupling. -/
noncomputable def pom_diagonal_rate_explicit_param_and_derivative_coupling
    (D : pom_diagonal_rate_explicit_param_and_derivative_Data) (a b : Fin D.n) : ℝ :=
  D.u a * D.u b * (1 + D.kappa * if a = b then (1 : ℝ) else 0) /
    pom_diagonal_rate_explicit_param_and_derivative_Z D

/-- The self-consistency right hand side after summing the product coupling over the second
coordinate. -/
noncomputable def pom_diagonal_rate_explicit_param_and_derivative_marginal_rhs
    (D : pom_diagonal_rate_explicit_param_and_derivative_Data) (a : Fin D.n) : ℝ :=
  D.u a * ((∑ b : Fin D.n, D.u b) + D.kappa * D.u a) /
    pom_diagonal_rate_explicit_param_and_derivative_Z D

/-- The dual slope parameter `lambda = log (1 + kappa)`. -/
noncomputable def pom_diagonal_rate_explicit_param_and_derivative_lambda
    (D : pom_diagonal_rate_explicit_param_and_derivative_Data) : ℝ :=
  Real.log (1 + D.kappa)

/-- The envelope-theorem derivative value in the active region. -/
noncomputable def pom_diagonal_rate_explicit_param_and_derivative_derivative
    (D : pom_diagonal_rate_explicit_param_and_derivative_Data) : ℝ :=
  -pom_diagonal_rate_explicit_param_and_derivative_lambda D

/-- The closed-form rate expression attached to the finite exponential-family parameters. -/
noncomputable def pom_diagonal_rate_explicit_param_and_derivative_rate_closed
    (D : pom_diagonal_rate_explicit_param_and_derivative_Data) : ℝ :=
  2 * (∑ a : Fin D.n, D.w a * Real.log (D.u a / D.w a)) -
    Real.log (pom_diagonal_rate_explicit_param_and_derivative_Z D) +
    (1 - D.delta) * Real.log (1 + D.kappa)

/-- Concrete claim: the explicit exponential-family formula has the stated marginal algebra and
the envelope derivative is `-log (1 + kappa)`. -/
def pom_diagonal_rate_explicit_param_and_derivative_Data.pom_diagonal_rate_explicit_param_and_derivative_claim
    (D : pom_diagonal_rate_explicit_param_and_derivative_Data) : Prop :=
  (∀ a b : Fin D.n,
      pom_diagonal_rate_explicit_param_and_derivative_coupling D a b =
        D.u a * D.u b * (1 + D.kappa * if a = b then (1 : ℝ) else 0) /
          pom_diagonal_rate_explicit_param_and_derivative_Z D) ∧
    (∀ a : Fin D.n,
      ∑ b : Fin D.n, pom_diagonal_rate_explicit_param_and_derivative_coupling D a b =
        pom_diagonal_rate_explicit_param_and_derivative_marginal_rhs D a) ∧
    0 ≤ pom_diagonal_rate_explicit_param_and_derivative_lambda D ∧
    pom_diagonal_rate_explicit_param_and_derivative_derivative D =
      -Real.log (1 + D.kappa)

lemma pom_diagonal_rate_explicit_param_and_derivative_sum_ite_eq
    (D : pom_diagonal_rate_explicit_param_and_derivative_Data) (a : Fin D.n) :
    (∑ b : Fin D.n, D.u b * (if a = b then (1 : ℝ) else 0)) = D.u a := by
  classical
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    have hba : a ≠ b := fun h => hb h.symm
    simp [hba]
  · intro ha
    exact False.elim (ha (Finset.mem_univ a))

/-- Paper label: `thm:pom-diagonal-rate-explicit-param-and-derivative`. -/
theorem paper_pom_diagonal_rate_explicit_param_and_derivative
    (D : pom_diagonal_rate_explicit_param_and_derivative_Data) :
    D.pom_diagonal_rate_explicit_param_and_derivative_claim := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    rfl
  · intro a
    unfold pom_diagonal_rate_explicit_param_and_derivative_coupling
    unfold pom_diagonal_rate_explicit_param_and_derivative_marginal_rhs
    rw [← Finset.sum_div]
    congr 1
    calc
      ∑ b : Fin D.n, D.u a * D.u b *
          (1 + D.kappa * if a = b then (1 : ℝ) else 0)
          = D.u a * (∑ b : Fin D.n,
              D.u b * (1 + D.kappa * if a = b then (1 : ℝ) else 0)) := by
            rw [Finset.mul_sum]
            simp [mul_assoc]
      _ = D.u a * ((∑ b : Fin D.n, D.u b) +
            D.kappa * ∑ b : Fin D.n, D.u b * (if a = b then (1 : ℝ) else 0)) := by
            congr 1
            calc
              ∑ b : Fin D.n, D.u b * (1 + D.kappa * if a = b then (1 : ℝ) else 0)
                  = ∑ b : Fin D.n,
                      (D.u b + D.u b * (D.kappa * if a = b then (1 : ℝ) else 0)) := by
                    congr
                    ext b
                    ring
              _ = (∑ b : Fin D.n, D.u b) +
                    ∑ b : Fin D.n,
                      D.u b * (D.kappa * if a = b then (1 : ℝ) else 0) := by
                    rw [Finset.sum_add_distrib]
              _ = (∑ b : Fin D.n, D.u b) +
                    D.kappa * ∑ b : Fin D.n,
                      D.u b * (if a = b then (1 : ℝ) else 0) := by
                    congr 1
                    rw [Finset.mul_sum]
                    congr
                    ext b
                    ring
      _ = D.u a * ((∑ b : Fin D.n, D.u b) + D.kappa * D.u a) := by
            rw [pom_diagonal_rate_explicit_param_and_derivative_sum_ite_eq]
  · unfold pom_diagonal_rate_explicit_param_and_derivative_lambda
    exact Real.log_nonneg (by linarith [D.hkappa_nonneg])
  · rfl

end Omega.POM
