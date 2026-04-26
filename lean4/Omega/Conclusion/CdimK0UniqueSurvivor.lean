import Omega.Conclusion.FiniteRankExactAdditiveUniqueExtension
import Omega.CircleDimension.ShortExactAdditivity

namespace Omega.Conclusion

open Omega.CircleDimension

/-- Concrete `K₀` surrogate for finitely generated abelian groups: only the free rank survives. -/
def conclusion_cdim_k0_unique_survivor_class (r t : Nat) : Nat :=
  circleDim r t

/-- Paper-facing bookkeeping version of `K₀(Ab_fg) ≃ ℤ`: the torsion class vanishes, every class
is a multiple of `[ℤ]`, and any normalized short-exact additive invariant agrees with this
surviving rank class. -/
def paper_conclusion_cdim_k0_unique_survivor_statement : Prop :=
  (∀ n : Nat,
      conclusion_cdim_k0_unique_survivor_class 1 0 =
        conclusion_cdim_k0_unique_survivor_class 1 0 +
          conclusion_cdim_k0_unique_survivor_class 0 n) ∧
    (∀ n : Nat, conclusion_cdim_k0_unique_survivor_class 0 n = 0) ∧
    (∀ rA rC tA tB tC : Nat,
      conclusion_cdim_k0_unique_survivor_class (rA + rC) tB =
        conclusion_cdim_k0_unique_survivor_class rA tA +
          conclusion_cdim_k0_unique_survivor_class rC tC) ∧
    (∀ r t : Nat,
      conclusion_cdim_k0_unique_survivor_class r t =
        r * conclusion_cdim_k0_unique_survivor_class 1 0) ∧
    ∀ δ : Nat → Nat → Nat,
      (∀ a b c d : Nat, δ (a + b) (c + d) = δ a c + δ b d) →
      (∀ t : Nat, δ 0 t = 0) →
      (δ 1 0 = 1) →
      ∀ r t : Nat, δ r t = conclusion_cdim_k0_unique_survivor_class r t

/-- Paper label: `thm:conclusion-cdim-k0-unique-survivor`. -/
theorem paper_conclusion_cdim_k0_unique_survivor :
    paper_conclusion_cdim_k0_unique_survivor_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simp [conclusion_cdim_k0_unique_survivor_class, circleDim]
  · intro n
    simp [conclusion_cdim_k0_unique_survivor_class, circleDim]
  · intro rA rC tA tB tC
    simpa [conclusion_cdim_k0_unique_survivor_class] using
      (paper_killo_cdim_short_exact_additivity rA (rA + rC) rC tA tB tC 0 0 rfl).1
  · intro r t
    simp [conclusion_cdim_k0_unique_survivor_class, circleDim]
  · intro δ hAdd hTors hNorm r t
    exact (paper_conclusion_finite_rank_exact_additive_unique_extension δ hTors hAdd hNorm).1 r t

end Omega.Conclusion
