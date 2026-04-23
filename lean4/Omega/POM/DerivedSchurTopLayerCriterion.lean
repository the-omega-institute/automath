import Mathlib.Tactic
import Omega.POM.HookChannelLeadingTermCancellation

namespace Omega.POM

noncomputable section

open SchurPartitionIndex

/-- The top-layer coefficient `b_λ` in the two-partition seed model. -/
def derived_schur_top_layer_criterion_b_lambda : SchurPartitionIndex → ℝ
  | cycle => 1
  | split => 0

/-- The common exponential factor `f^λ` inherited from the Schur seed. -/
def derived_schur_top_layer_criterion_f_lambda (lam : SchurPartitionIndex) : ℝ :=
  schurDegree lam

/-- The leading top-layer coefficient after multiplying by the Schur degree. -/
def derived_schur_top_layer_criterion_leading_coeff (lam : SchurPartitionIndex) : ℝ :=
  derived_schur_top_layer_criterion_f_lambda lam *
    derived_schur_top_layer_criterion_b_lambda lam

/-- Visibility of the top exponential layer. -/
def derived_schur_top_layer_criterion_visible (lam : SchurPartitionIndex) : Prop :=
  derived_schur_top_layer_criterion_leading_coeff lam ≠ 0

/-- Cancellation of the top exponential layer. -/
def derived_schur_top_layer_criterion_cancelled (lam : SchurPartitionIndex) : Prop :=
  derived_schur_top_layer_criterion_leading_coeff lam = 0

/-- Paper label: `thm:derived-schur-top-layer-criterion`. In the `S_2` seed model, the leading
top-layer coefficient is `f^λ b_λ`; hence visibility and cancellation are determined exactly by
whether `b_λ` vanishes. -/
def derived_schur_top_layer_criterion_statement : Prop :=
  (∀ lam : SchurPartitionIndex,
      derived_schur_top_layer_criterion_leading_coeff lam =
        derived_schur_top_layer_criterion_f_lambda lam *
          derived_schur_top_layer_criterion_b_lambda lam) ∧
    (∀ lam : SchurPartitionIndex,
      derived_schur_top_layer_criterion_visible lam ↔
        derived_schur_top_layer_criterion_b_lambda lam ≠ 0) ∧
    (∀ lam : SchurPartitionIndex,
      derived_schur_top_layer_criterion_cancelled lam ↔
        derived_schur_top_layer_criterion_b_lambda lam = 0)

theorem paper_derived_schur_top_layer_criterion :
    derived_schur_top_layer_criterion_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro lam
    rfl
  · intro lam
    cases lam <;>
      simp [derived_schur_top_layer_criterion_visible,
        derived_schur_top_layer_criterion_leading_coeff,
        derived_schur_top_layer_criterion_f_lambda,
        derived_schur_top_layer_criterion_b_lambda, schurDegree]
  · intro lam
    cases lam <;>
      simp [derived_schur_top_layer_criterion_cancelled,
        derived_schur_top_layer_criterion_leading_coeff,
        derived_schur_top_layer_criterion_f_lambda,
        derived_schur_top_layer_criterion_b_lambda, schurDegree]

end

end Omega.POM
