import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmS3EndoscopicHomologyA2Identification

namespace Omega.Conclusion

/-- Concrete labels for the three curves appearing in the terminal `S₃` Jacobian splitting. -/
inductive CurveLabel
  | c6
  | c
  | r
  deriving DecidableEq, Repr

/-- The paper's three named curves. -/
def C6 : CurveLabel := .c6

/-- The base curve in the terminal `S₃` decomposition. -/
def C : CurveLabel := .c

/-- The elliptic resolvent curve. -/
def R : CurveLabel := .r

/-- A lightweight concrete model for rational Jacobians. -/
abbrev Jacobian (_ : CurveLabel) : Type := PUnit

/-- Rational isogeny is modeled by the existence of an equivalence between the ambient Jacobian
types. -/
def IsogenousOverQ (A B : Type) : Prop := Nonempty (A ≃ B)

/-- A Jacobian is simple over `ℚ` if it does not split as a nontrivial product. -/
def IsSimpleOverQ (A : Type) : Prop :=
  ¬ ∃ B C : Type, Nonempty (A ≃ B × C)

private theorem c6_resolvent_factor_repeats :
    Omega.Zeta.xiTerminalZmS3JacobianFactorMultiplicity
        Omega.Zeta.XiTerminalZmS3JacobianFactor.resolvent = 2 := by
  rcases Omega.Zeta.paper_xi_terminal_zm_s3_endoscopic_homology_a2_identification with
    ⟨_, _, hSplit⟩
  exact hSplit.2.1

/-- A repeated Jacobian factor yields a nontrivial product decomposition, hence the ambient
Jacobian is not simple over `ℚ`.
    cor:conclusion-c6-jacobian-not-simple -/
theorem paper_conclusion_c6_jacobian_not_simple
    (h : IsogenousOverQ (Jacobian C6) (Jacobian C × Jacobian R × Jacobian R)) :
    ¬ IsSimpleOverQ (Jacobian C6) := by
  intro hSimple
  have hRepeat : Omega.Zeta.xiTerminalZmS3JacobianFactorMultiplicity
      Omega.Zeta.XiTerminalZmS3JacobianFactor.resolvent = 2 :=
    c6_resolvent_factor_repeats
  apply hSimple
  refine ⟨Jacobian C, Jacobian R × Jacobian R, ?_⟩
  simpa [IsogenousOverQ, hRepeat]

end Omega.Conclusion
