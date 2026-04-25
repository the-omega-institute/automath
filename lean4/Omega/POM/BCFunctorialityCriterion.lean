import Mathlib.Tactic
import Omega.POM.BeckChevalleyAmgmDefectIdentity

namespace Omega.POM

noncomputable section

/-- Pointwise equality of the sequential and direct lifts in the concrete two-fiber model. -/
def pom_bc_functoriality_criterion_operator_equality (a b : ℕ) : Prop :=
  sequentialUniformLift a b = directUniformLift a b

/-- Vanishing of the Beck--Chevalley KL defect in the concrete two-fiber model. -/
def pom_bc_functoriality_criterion_zero_kl_defect (a b : ℕ) : Prop :=
  klDiv (sequentialUniformLift a b) (directUniformLift a b) = 0

/-- Fiberwise constancy means that the two visible inner fibers have the same cardinality. -/
def pom_bc_functoriality_criterion_fiberwise_constancy (a b : ℕ) : Prop :=
  a = b

lemma pom_bc_functoriality_criterion_constancy_of_operator_equality
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hEq : pom_bc_functoriality_criterion_operator_equality a b) :
    pom_bc_functoriality_criterion_fiberwise_constancy a b := by
  let i0 : Fin a := ⟨0, ha⟩
  have hEval : 1 / (2 * (a : ℝ)) = 1 / ((a : ℝ) + b) := by
    simpa [pom_bc_functoriality_criterion_operator_equality, sequentialUniformLift, directUniformLift]
      using congrFun hEq (Sum.inl i0)
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have habR : ((a : ℝ) + b) ≠ 0 := by positivity
  have hCardR : (a : ℝ) = b := by
    field_simp [haR, hbR, habR] at hEval
    nlinarith
  exact_mod_cast hCardR

lemma pom_bc_functoriality_criterion_operator_equality_of_constancy
    (a b : ℕ) (ha : 0 < a)
    (hConst : pom_bc_functoriality_criterion_fiberwise_constancy a b) :
    pom_bc_functoriality_criterion_operator_equality a b := by
  subst hConst
  funext x
  rcases x with _ | _
  · have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
    simp [sequentialUniformLift, directUniformLift]
    field_simp [haR]
    norm_num
  · have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
    simp [sequentialUniformLift, directUniformLift]
    field_simp [haR]
    norm_num

/-- Paper label: `cor:pom-bc-functoriality-criterion`. In the concrete two-fiber
Beck--Chevalley model, pointwise equality of the sequential and direct lifted distributions,
vanishing of the KL defect, and fiberwise constancy of the two visible fibers are equivalent. -/
theorem paper_pom_bc_functoriality_criterion {X Y Z : Type*} (f : X → Y) (g : Y → Z) :
    ∀ a b : ℕ, 0 < a → 0 < b →
      (pom_bc_functoriality_criterion_operator_equality a b ↔
        pom_bc_functoriality_criterion_zero_kl_defect a b) ∧
      (pom_bc_functoriality_criterion_zero_kl_defect a b ↔
        pom_bc_functoriality_criterion_fiberwise_constancy a b) ∧
      (pom_bc_functoriality_criterion_fiberwise_constancy a b ↔
        pom_bc_functoriality_criterion_operator_equality a b) := by
  let _ := f
  let _ := g
  intro a b ha hb
  have hZeroIff :
      pom_bc_functoriality_criterion_zero_kl_defect a b ↔
        pom_bc_functoriality_criterion_fiberwise_constancy a b := by
    unfold pom_bc_functoriality_criterion_zero_kl_defect
      pom_bc_functoriality_criterion_fiberwise_constancy
    rcases paper_pom_bc_amgm_defect_identity a b ha hb with ⟨_, _, hZero⟩
    exact hZero
  have hConstIffEq :
      pom_bc_functoriality_criterion_fiberwise_constancy a b ↔
        pom_bc_functoriality_criterion_operator_equality a b := by
    constructor
    · intro hConst
      exact pom_bc_functoriality_criterion_operator_equality_of_constancy a b ha hConst
    · intro hEq
      exact pom_bc_functoriality_criterion_constancy_of_operator_equality a b ha hb hEq
  refine ⟨?_, hZeroIff, hConstIffEq⟩
  rw [hZeroIff, hConstIffEq]

end

end Omega.POM
