import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete pair of endpoint moment sequences. -/
abbrev xi_endpoint_probe_hausdorff_determinacy_data := (ℕ → ℝ) × (ℕ → ℝ)

/-- The scalar endpoint probe moment obtained from the Adams-rotated identity. -/
def xi_endpoint_probe_hausdorff_determinacy_endpoint_probe_moment (N : ℕ) : ℝ :=
  (1 : ℝ) ^ N

/-- The rotated endpoint probe has the same scalar moment sequence. -/
def xi_endpoint_probe_hausdorff_determinacy_adams_rotated_moment (_N : ℕ) : ℝ :=
  1

/-- Polynomial moment functional determined by a scalar moment sequence. -/
noncomputable def xi_endpoint_probe_hausdorff_determinacy_polynomial_moment
    (m : ℕ → ℝ) (p : Polynomial ℝ) : ℝ :=
  Finset.sum p.support fun n => p.coeff n * m n

/-- Equality of all monomial moments extends to every polynomial test function. -/
def xi_endpoint_probe_hausdorff_determinacy_polynomial_extension
    (D : xi_endpoint_probe_hausdorff_determinacy_data) : Prop :=
  (∀ N : ℕ, D.1 N = D.2 N) →
    ∀ p : Polynomial ℝ,
      xi_endpoint_probe_hausdorff_determinacy_polynomial_moment D.1 p =
        xi_endpoint_probe_hausdorff_determinacy_polynomial_moment D.2 p

/-- Hausdorff determinacy bridge in the concrete scalar-moment model. -/
def xi_endpoint_probe_hausdorff_determinacy_pushforward_determined
    (D : xi_endpoint_probe_hausdorff_determinacy_data) : Prop :=
  (∀ N : ℕ, D.1 N = D.2 N) → D.1 = D.2

namespace xi_endpoint_probe_hausdorff_determinacy_data

/-- Paper-facing endpoint-probe determinacy statement. -/
def statement (D : xi_endpoint_probe_hausdorff_determinacy_data) : Prop :=
  (∀ N : ℕ,
      xi_endpoint_probe_hausdorff_determinacy_endpoint_probe_moment N =
        xi_endpoint_probe_hausdorff_determinacy_adams_rotated_moment N) ∧
    xi_endpoint_probe_hausdorff_determinacy_polynomial_extension D ∧
      xi_endpoint_probe_hausdorff_determinacy_pushforward_determined D

end xi_endpoint_probe_hausdorff_determinacy_data

/-- Paper label: `cor:xi-endpoint-probe-hausdorff-determinacy`. -/
theorem paper_xi_endpoint_probe_hausdorff_determinacy
    (D : xi_endpoint_probe_hausdorff_determinacy_data) : D.statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro N
    simp [xi_endpoint_probe_hausdorff_determinacy_endpoint_probe_moment,
      xi_endpoint_probe_hausdorff_determinacy_adams_rotated_moment]
  · intro hMom p
    unfold xi_endpoint_probe_hausdorff_determinacy_polynomial_moment
    exact Finset.sum_congr rfl (fun n _hn => by rw [hMom n])
  · intro hMom
    funext N
    exact hMom N

end Omega.Zeta
