import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Zeta.XiAddressDefectLaw
import Omega.Zeta.XiOffsetNullTypeSafety
import Omega.Zeta.XiPrimeRegisterHistoryInverseLimit

namespace Omega.Zeta

/-- Semantic `NULL`: the point is not on the unitary slice, so it is not semantically addressable
inside the visible `xi` readout. -/
def xiSemanticNullBranch (L : ℝ) (s : ℂ) : Prop :=
  ¬ xiOffsetUnitarySlice L s

/-- Protocol `NULL`: the Peter-Weyl closure rejects the off-slice point. -/
def xiProtocolNullBranch (L : ℝ) (s : ℂ) : Prop :=
  xiOffsetPwClosureNull L s

/-- Collision `NULL`: an auxiliary register is required, and the registered readout must separate
every visible fiber while paying the corresponding entropy budget. -/
def xiCollisionNullBranch {A X R : Type*} [Fintype A] [Fintype R] [DecidableEq X]
    (fold : A → X) (r : A → R) : Prop :=
  xiFiberwiseSeparated fold r ∧ xiFiberUniformLiftCostBound fold r

/-- Explicit budget witness for the auxiliary register needed to injectivize the readout. -/
def xiPrimeRegisterBudgetWitness {A X R : Type*} [Fintype A] [Fintype R] [DecidableEq X]
    (fold : A → X) (_r : A → R) : Prop :=
  ∃ B : ℝ, B = xiConditionalEntropyProxy R ∧
    ∀ a : A, Real.log (xiAddressFiberCard fold (fold a)) ≤ B

/-- Paper-facing `NULL` decomposition: off-slice points supply the semantic and protocol branches,
while any injectivizing register packages the collision branch together with its sharp logarithmic
budget witness and the finite prime-register encodings.
    prop:xi-null-three-way -/
def paper_xi_null_three_way_statement : Prop :=
  ∀ {A X R : Type*} [Fintype A] [Fintype R] [DecidableEq X],
    ∀ {L : ℝ} {s : ℂ},
      1 < L →
      s.re ≠ 1 / 2 →
      ∀ (fold : A → X) (r : A → R),
        Function.Injective (fun a => (fold a, r a)) →
          xiSemanticNullBranch L s ∧
            xiProtocolNullBranch L s ∧
            xiCollisionNullBranch fold r ∧
            xiPrimeRegisterBudgetWitness fold r ∧
            (∀ k : ℕ, Function.Injective (xiPrimeRegisterEncode (X := X) k)) ∧
            Nonempty (XiPrimeRegisterCompatibleFamily X ≃ XiPrimeRegisterStream X)

theorem paper_xi_null_three_way : paper_xi_null_three_way_statement := by
  intro A X R _ _ _ L s hL hs fold r hinj
  rcases paper_xi_offset_null_type_safety hL hs with ⟨_, hSemantic, hProtocol⟩
  have hCollision := paper_xi_address_defect_law (A := A) (X := X) (R := R) fold r hinj
  rcases paper_xi_prime_register_history_inverse_limit X with ⟨hEncode, hLimit⟩
  refine ⟨hSemantic, hProtocol, hCollision, ?_, hEncode, hLimit⟩
  refine ⟨xiConditionalEntropyProxy R, rfl, ?_⟩
  intro a
  exact hCollision.2 a

end Omega.Zeta
