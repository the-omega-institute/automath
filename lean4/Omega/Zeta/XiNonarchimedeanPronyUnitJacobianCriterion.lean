import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Omega.Zeta.HankelVandermonde2
import Omega.Zeta.XiNonarchimedeanPronyHenselNewtonInversion

namespace Omega.Zeta

/-- Concrete two-node nonarchimedean Prony data. The unit-weight hypotheses pin the Jacobian and
Hankel valuations to the collision gap alone, and the existing Hensel-Newton theorem supplies the
local inverse statement. -/
structure XiNonarchimedeanPronyUnitJacobianCriterionData where
  p : ℕ
  a₁ : ℤ
  a₂ : ℤ
  ω₁ : ℤ
  ω₂ : ℤ
  hp : Nat.Prime p
  hω₁ : ω₁ ≠ 0
  hω₂ : ω₂ ≠ 0
  hgap : a₁ ≠ a₂
  hω₁Unit : padicValRat p (ω₁ : ℚ) = 0
  hω₂Unit : padicValRat p (ω₂ : ℚ) = 0

namespace XiNonarchimedeanPronyUnitJacobianCriterionData

def unitCriterion (D : XiNonarchimedeanPronyUnitJacobianCriterionData) : Prop :=
  padicValRat D.p ((pronyJacobian2 D.a₁ D.a₂ D.ω₁ D.ω₂).det : ℚ) = 0 ↔
    padicValRat D.p (hankel2 D.ω₁ D.ω₂ D.a₁ D.a₂ : ℚ) = 0 ∧
      padicValRat D.p ((D.a₂ - D.a₁ : ℤ) : ℚ) = 0

def localAnalyticInverse (D : XiNonarchimedeanPronyUnitJacobianCriterionData) : Prop :=
  ∀ target : Fin 4 → ℚ, ∃! correction : Fin 4 → ℚ,
    xiPronyLinearizedNewtonMap2 D.a₁ D.a₂ D.ω₁ D.ω₂ correction = target

private theorem jacobianVal_eq_four_gapVal (D : XiNonarchimedeanPronyUnitJacobianCriterionData) :
    padicValRat D.p ((pronyJacobian2 D.a₁ D.a₂ D.ω₁ D.ω₂).det : ℚ) =
      (4 : ℤ) * padicValRat D.p ((D.a₂ - D.a₁ : ℤ) : ℚ) := by
  simpa [D.hω₁Unit, D.hω₂Unit] using
    (paper_xi_nonarchimedean_prony_hensel_newton_inversion
      D.p D.a₁ D.a₂ D.ω₁ D.ω₂ D.hp D.hω₁ D.hω₂ D.hgap).1

private theorem hankelVal_eq_two_gapVal (D : XiNonarchimedeanPronyUnitJacobianCriterionData) :
    padicValRat D.p (hankel2 D.ω₁ D.ω₂ D.a₁ D.a₂ : ℚ) =
      (2 : ℤ) * padicValRat D.p ((D.a₂ - D.a₁ : ℤ) : ℚ) := by
  haveI : Fact D.p.Prime := ⟨D.hp⟩
  have hω₁q : (D.ω₁ : ℚ) ≠ 0 := by
    exact_mod_cast D.hω₁
  have hω₂q : (D.ω₂ : ℚ) ≠ 0 := by
    exact_mod_cast D.hω₂
  have hgapZ : D.a₂ - D.a₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm D.hgap)
  have hgapQ : (((D.a₂ - D.a₁ : ℤ) : ℚ)) ≠ 0 := by
    exact_mod_cast hgapZ
  have hhankel :
      (hankel2 D.ω₁ D.ω₂ D.a₁ D.a₂ : ℚ) =
        (D.ω₁ : ℚ) * (D.ω₂ : ℚ) * (((D.a₂ - D.a₁ : ℤ) : ℚ) ^ 2) := by
    simpa [mul_assoc] using
      congrArg (fun z : ℤ => (z : ℚ)) (hankel2_vandermonde_square D.ω₁ D.ω₂ D.a₁ D.a₂)
  calc
    padicValRat D.p (hankel2 D.ω₁ D.ω₂ D.a₁ D.a₂ : ℚ)
        = padicValRat D.p ((D.ω₁ : ℚ) * (D.ω₂ : ℚ) * (((D.a₂ - D.a₁ : ℤ) : ℚ) ^ 2)) := by
            rw [hhankel]
    _ = padicValRat D.p (D.ω₁ : ℚ) +
          padicValRat D.p ((D.ω₂ : ℚ) * (((D.a₂ - D.a₁ : ℤ) : ℚ) ^ 2)) := by
            simpa [mul_assoc] using
              padicValRat.mul (p := D.p) (q := (D.ω₁ : ℚ))
                (r := (D.ω₂ : ℚ) * (((D.a₂ - D.a₁ : ℤ) : ℚ) ^ 2))
                hω₁q (mul_ne_zero hω₂q (pow_ne_zero 2 hgapQ))
    _ = padicValRat D.p (D.ω₁ : ℚ) + padicValRat D.p (D.ω₂ : ℚ) +
          padicValRat D.p ((((D.a₂ - D.a₁ : ℤ) : ℚ) ^ 2)) := by
            rw [padicValRat.mul hω₂q (pow_ne_zero 2 hgapQ)]
            ring
    _ = padicValRat D.p (D.ω₁ : ℚ) + padicValRat D.p (D.ω₂ : ℚ) +
          (2 : ℤ) * padicValRat D.p ((D.a₂ - D.a₁ : ℤ) : ℚ) := by
            rw [padicValRat.pow hgapQ]
            norm_num
    _ = (2 : ℤ) * padicValRat D.p ((D.a₂ - D.a₁ : ℤ) : ℚ) := by
          rw [D.hω₁Unit, D.hω₂Unit]
          ring

end XiNonarchimedeanPronyUnitJacobianCriterionData

open XiNonarchimedeanPronyUnitJacobianCriterionData

/-- Paper label: `cor:xi-nonarchimedean-prony-unit-jacobian-criterion`. -/
theorem paper_xi_nonarchimedean_prony_unit_jacobian_criterion
    (D : XiNonarchimedeanPronyUnitJacobianCriterionData) :
    D.unitCriterion ∧ D.localAnalyticInverse := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro hdet
      have hgap0 : padicValRat D.p ((D.a₂ - D.a₁ : ℤ) : ℚ) = 0 := by
        rw [jacobianVal_eq_four_gapVal] at hdet
        linarith
      refine ⟨?_, hgap0⟩
      rw [hankelVal_eq_two_gapVal, hgap0]
      norm_num
    · rintro ⟨_, hgap0⟩
      rw [jacobianVal_eq_four_gapVal, hgap0]
      norm_num
  · exact
      (paper_xi_nonarchimedean_prony_hensel_newton_inversion
        D.p D.a₁ D.a₂ D.ω₁ D.ω₂ D.hp D.hω₁ D.hω₂ D.hgap).2

end Omega.Zeta
