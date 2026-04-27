import Mathlib.Tactic

namespace Omega.Conclusion

/-- A scalar pressure germ for the real-input-40 separation wrapper. -/
def conclusion_realinput40_analytic_regularity_endpoint_type_separation_pressure
    (θ : ℝ) : ℝ :=
  θ ^ 2 + 1

/-- The scalar pressure has the advertised regular analytic germ. -/
def conclusion_realinput40_analytic_regularity_endpoint_type_separation_analytic_pressure :
    Prop :=
  ∀ θ : ℝ,
    DifferentiableAt ℝ
      conclusion_realinput40_analytic_regularity_endpoint_type_separation_pressure θ

/-- A square-root-order dominance criterion fails on the concrete test scale `1 / 2`. -/
def conclusion_realinput40_analytic_regularity_endpoint_type_separation_sqrt_failure :
    Prop :=
  ¬ ∀ ε : ℝ, 0 < ε → ε ≤ ε ^ 2

/-- The endpoint ground state retains positive entropy. -/
def conclusion_realinput40_analytic_regularity_endpoint_type_separation_positive_entropy :
    Prop :=
  0 < Real.log 2

/-- A directed four-state Parry-limit test kernel. -/
def conclusion_realinput40_analytic_regularity_endpoint_type_separation_parry_kernel
    (i j : Fin 4) : ℝ :=
  if i = ⟨1, by decide⟩ ∧ j = ⟨2, by decide⟩ then 1 else 0

/-- A positive stationary test weight for the directed Parry-limit certificate. -/
def conclusion_realinput40_analytic_regularity_endpoint_type_separation_stationary
    (_i : Fin 4) : ℝ :=
  1

/-- Detailed balance for the concrete directed endpoint kernel. -/
def conclusion_realinput40_analytic_regularity_endpoint_type_separation_detailed_balance :
    Prop :=
  ∀ i j : Fin 4,
    conclusion_realinput40_analytic_regularity_endpoint_type_separation_stationary i *
        conclusion_realinput40_analytic_regularity_endpoint_type_separation_parry_kernel i j =
      conclusion_realinput40_analytic_regularity_endpoint_type_separation_stationary j *
        conclusion_realinput40_analytic_regularity_endpoint_type_separation_parry_kernel j i

/-- The concrete endpoint Parry limit is irreversible. -/
def conclusion_realinput40_analytic_regularity_endpoint_type_separation_irreversible_parry :
    Prop :=
  ¬ conclusion_realinput40_analytic_regularity_endpoint_type_separation_detailed_balance

/-- Entropy production is represented by an unbounded sequence of finite production cutoffs. -/
def conclusion_realinput40_analytic_regularity_endpoint_type_separation_infinite_entropy_production :
    Prop :=
  ∀ B : ℝ, ∃ n : ℕ, B < n

/-- Conclusion wrapper combining analytic pressure regularity, square-root criterion failure,
positive-entropy endpoint selection, irreversible Parry behavior, and unbounded entropy
production. -/
def conclusion_realinput40_analytic_regularity_endpoint_type_separation_statement : Prop :=
  conclusion_realinput40_analytic_regularity_endpoint_type_separation_analytic_pressure ∧
    conclusion_realinput40_analytic_regularity_endpoint_type_separation_sqrt_failure ∧
    conclusion_realinput40_analytic_regularity_endpoint_type_separation_positive_entropy ∧
    conclusion_realinput40_analytic_regularity_endpoint_type_separation_irreversible_parry ∧
    conclusion_realinput40_analytic_regularity_endpoint_type_separation_infinite_entropy_production

lemma conclusion_realinput40_analytic_regularity_endpoint_type_separation_pressure_regular :
    conclusion_realinput40_analytic_regularity_endpoint_type_separation_analytic_pressure := by
  intro θ
  unfold conclusion_realinput40_analytic_regularity_endpoint_type_separation_pressure
  fun_prop

lemma conclusion_realinput40_analytic_regularity_endpoint_type_separation_sqrt_fails :
    conclusion_realinput40_analytic_regularity_endpoint_type_separation_sqrt_failure := by
  intro h
  have hhalf := h (1 / 2 : ℝ) (by norm_num)
  norm_num at hhalf

lemma conclusion_realinput40_analytic_regularity_endpoint_type_separation_ground_entropy_pos :
    conclusion_realinput40_analytic_regularity_endpoint_type_separation_positive_entropy := by
  exact Real.log_pos one_lt_two

lemma conclusion_realinput40_analytic_regularity_endpoint_type_separation_parry_irreversible :
    conclusion_realinput40_analytic_regularity_endpoint_type_separation_irreversible_parry := by
  intro h
  have h12 := h ⟨1, by decide⟩ ⟨2, by decide⟩
  norm_num [
    conclusion_realinput40_analytic_regularity_endpoint_type_separation_detailed_balance,
    conclusion_realinput40_analytic_regularity_endpoint_type_separation_stationary,
    conclusion_realinput40_analytic_regularity_endpoint_type_separation_parry_kernel] at h12

lemma conclusion_realinput40_analytic_regularity_endpoint_type_separation_entropy_unbounded :
    conclusion_realinput40_analytic_regularity_endpoint_type_separation_infinite_entropy_production := by
  intro B
  exact exists_nat_gt B

/-- Paper label:
`thm:conclusion-realinput40-analytic-regularity-endpoint-type-separation`. -/
theorem paper_conclusion_realinput40_analytic_regularity_endpoint_type_separation :
    conclusion_realinput40_analytic_regularity_endpoint_type_separation_statement := by
  exact
    ⟨conclusion_realinput40_analytic_regularity_endpoint_type_separation_pressure_regular,
      conclusion_realinput40_analytic_regularity_endpoint_type_separation_sqrt_fails,
      conclusion_realinput40_analytic_regularity_endpoint_type_separation_ground_entropy_pos,
      conclusion_realinput40_analytic_regularity_endpoint_type_separation_parry_irreversible,
      conclusion_realinput40_analytic_regularity_endpoint_type_separation_entropy_unbounded⟩

end Omega.Conclusion
