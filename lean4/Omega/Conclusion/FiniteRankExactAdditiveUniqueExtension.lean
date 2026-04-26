import Omega.Conclusion.CdimqUniqueExactExtension

namespace Omega.Conclusion

open Omega.CircleDimension

/-- Concrete conclusion-level package for the unique exact-additive extension on finite-rank
abelian bookkeeping data: the invariant agrees with `circleDim`, hence with the rational rank, and
is unchanged by torsion kernel/cokernel defects. -/
def conclusion_finite_rank_exact_additive_unique_extension_statement
    (δ : Nat → Nat → Nat) : Prop :=
  ∀ (_hTors : ∀ t : Nat, δ 0 t = 0)
    (_hAdd : ∀ a b c d : Nat, δ (a + b) (c + d) = δ a c + δ b d)
    (_hNorm : δ 1 0 = 1),
    (∀ r t : Nat, δ r t = circleDim r t) ∧
      (∀ r t : Nat, δ r t = r) ∧
      (∀ r tG tH : Nat, δ r tG = δ r tH)

/-- Paper label: `thm:conclusion-finite-rank-exact-additive-unique-extension`. -/
theorem paper_conclusion_finite_rank_exact_additive_unique_extension (δ : Nat → Nat → Nat) :
    conclusion_finite_rank_exact_additive_unique_extension_statement δ := by
  intro hTors hAdd hNorm
  have hrigid : ∀ r t : Nat, δ r t = circleDim r t :=
    paper_conclusion_cdimq_unique_exact_extension δ hTors hAdd hNorm
  refine ⟨hrigid, ?_, ?_⟩
  · intro r t
    simpa [circleDim] using hrigid r t
  · intro r tG tH
    calc
      δ r tG = circleDim r tG := hrigid r tG
      _ = circleDim r tH := circleDim_finite_extension r tG tH
      _ = δ r tH := (hrigid r tH).symm

end Omega.Conclusion
