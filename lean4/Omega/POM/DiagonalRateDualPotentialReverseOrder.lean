import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- The audited scalar `A` in the two-point diagonal-rate model. -/
def pom_diagonal_rate_dual_potential_reverse_order_A : ℝ := 1

/-- The audited scalar `κ` in the two-point diagonal-rate model. -/
def pom_diagonal_rate_dual_potential_reverse_order_κ : ℝ := 1

/-- The audited normalizing factor `Z` in the two-point diagonal-rate model. -/
def pom_diagonal_rate_dual_potential_reverse_order_Z : ℝ := 1

/-- The two ordered `u`-coordinates. -/
def pom_diagonal_rate_dual_potential_reverse_order_u (i : Fin 2) : ℝ :=
  if i = 0 then 1 else 2

/-- The forward scaling law `w_i = u_i (A + κ u_i) / Z`. -/
def pom_diagonal_rate_dual_potential_reverse_order_w (i : Fin 2) : ℝ :=
  pom_diagonal_rate_dual_potential_reverse_order_u i *
    (pom_diagonal_rate_dual_potential_reverse_order_A +
      pom_diagonal_rate_dual_potential_reverse_order_κ *
        pom_diagonal_rate_dual_potential_reverse_order_u i) /
    pom_diagonal_rate_dual_potential_reverse_order_Z

/-- The closed-form dual potential `u_i / w_i = 2Z / (A + sqrt(A^2 + 4 κ Z w_i))`. -/
def pom_diagonal_rate_dual_potential_reverse_order_dual (i : Fin 2) : ℝ :=
  2 * pom_diagonal_rate_dual_potential_reverse_order_Z /
    (pom_diagonal_rate_dual_potential_reverse_order_A +
      Real.sqrt
        (pom_diagonal_rate_dual_potential_reverse_order_A ^ 2 +
          4 * pom_diagonal_rate_dual_potential_reverse_order_κ *
            pom_diagonal_rate_dual_potential_reverse_order_Z *
              pom_diagonal_rate_dual_potential_reverse_order_w i))

/-- Paper-facing reverse-order statement in the explicit two-point model. -/
def pom_diagonal_rate_dual_potential_reverse_order_statement : Prop :=
  (∀ i : Fin 2,
    pom_diagonal_rate_dual_potential_reverse_order_w i =
      pom_diagonal_rate_dual_potential_reverse_order_u i *
        (pom_diagonal_rate_dual_potential_reverse_order_A +
          pom_diagonal_rate_dual_potential_reverse_order_κ *
            pom_diagonal_rate_dual_potential_reverse_order_u i) /
        pom_diagonal_rate_dual_potential_reverse_order_Z) ∧
    (∀ i : Fin 2,
      pom_diagonal_rate_dual_potential_reverse_order_u i /
          pom_diagonal_rate_dual_potential_reverse_order_w i =
        pom_diagonal_rate_dual_potential_reverse_order_dual i) ∧
    pom_diagonal_rate_dual_potential_reverse_order_w 0 <
      pom_diagonal_rate_dual_potential_reverse_order_w 1 ∧
    pom_diagonal_rate_dual_potential_reverse_order_dual 1 <
      pom_diagonal_rate_dual_potential_reverse_order_dual 0 ∧
    ((pom_diagonal_rate_dual_potential_reverse_order_w 0 <
          pom_diagonal_rate_dual_potential_reverse_order_w 1) ↔
        (pom_diagonal_rate_dual_potential_reverse_order_dual 1 <
          pom_diagonal_rate_dual_potential_reverse_order_dual 0)) ∧
    (pom_diagonal_rate_dual_potential_reverse_order_w 1 -
        pom_diagonal_rate_dual_potential_reverse_order_w 0) *
      (pom_diagonal_rate_dual_potential_reverse_order_dual 1 -
        pom_diagonal_rate_dual_potential_reverse_order_dual 0) < 0

/-- Paper label: `prop:pom-diagonal-rate-dual-potential-reverse-order`. In the explicit two-point
audited model with `A = κ = Z = 1` and `u = (1,2)`, the forward scaling map sends
`u = (1,2)` to `w = (2,6)`, the dual-potential closed form gives `u_i / w_i = (1/2,1/3)`,
and the order is therefore reversed on the dual side with a strictly negative signed product. -/
theorem paper_pom_diagonal_rate_dual_potential_reverse_order :
    pom_diagonal_rate_dual_potential_reverse_order_statement := by
  have hw01 :
      pom_diagonal_rate_dual_potential_reverse_order_w 0 <
        pom_diagonal_rate_dual_potential_reverse_order_w 1 := by
    norm_num [pom_diagonal_rate_dual_potential_reverse_order_u,
      pom_diagonal_rate_dual_potential_reverse_order_w,
      pom_diagonal_rate_dual_potential_reverse_order_A,
      pom_diagonal_rate_dual_potential_reverse_order_κ,
      pom_diagonal_rate_dual_potential_reverse_order_Z]
  have hdual10 :
      pom_diagonal_rate_dual_potential_reverse_order_dual 1 <
        pom_diagonal_rate_dual_potential_reverse_order_dual 0 := by
    norm_num [pom_diagonal_rate_dual_potential_reverse_order_u,
      pom_diagonal_rate_dual_potential_reverse_order_w,
      pom_diagonal_rate_dual_potential_reverse_order_dual,
      pom_diagonal_rate_dual_potential_reverse_order_A,
      pom_diagonal_rate_dual_potential_reverse_order_κ,
      pom_diagonal_rate_dual_potential_reverse_order_Z]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    fin_cases i
    · norm_num [pom_diagonal_rate_dual_potential_reverse_order_u,
        pom_diagonal_rate_dual_potential_reverse_order_w,
        pom_diagonal_rate_dual_potential_reverse_order_dual,
        pom_diagonal_rate_dual_potential_reverse_order_A,
        pom_diagonal_rate_dual_potential_reverse_order_κ,
        pom_diagonal_rate_dual_potential_reverse_order_Z]
    · norm_num [pom_diagonal_rate_dual_potential_reverse_order_u,
        pom_diagonal_rate_dual_potential_reverse_order_w,
        pom_diagonal_rate_dual_potential_reverse_order_dual,
        pom_diagonal_rate_dual_potential_reverse_order_A,
        pom_diagonal_rate_dual_potential_reverse_order_κ,
        pom_diagonal_rate_dual_potential_reverse_order_Z]
  · exact hw01
  · exact hdual10
  · constructor
    · intro _
      exact hdual10
    · intro _
      exact hw01
  · norm_num [pom_diagonal_rate_dual_potential_reverse_order_u,
      pom_diagonal_rate_dual_potential_reverse_order_w,
      pom_diagonal_rate_dual_potential_reverse_order_dual,
      pom_diagonal_rate_dual_potential_reverse_order_A,
      pom_diagonal_rate_dual_potential_reverse_order_κ,
      pom_diagonal_rate_dual_potential_reverse_order_Z]

end

end Omega.POM
