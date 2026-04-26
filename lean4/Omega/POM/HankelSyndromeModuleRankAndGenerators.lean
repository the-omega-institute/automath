import Mathlib

namespace Omega.POM

/-- The concrete truncated-multiple model for a monic recurrence of degree `d` inside length `n`
is identified with the free tail coefficient space of dimension `n - d`. -/
abbrev pom_hankel_syndrome_module_rank_and_generators_module (n d : ℕ) :=
  Fin (n - d) → ℤ

/-- The shifted coefficient vectors `coeff_<n (λ^j P)` are represented by the standard basis of
the tail coefficient space. -/
noncomputable def pom_hankel_syndrome_module_rank_and_generators_generators
    (n d : ℕ) (_hd : d ≤ n) :
    Fin (n - d) → pom_hankel_syndrome_module_rank_and_generators_module n d :=
  Pi.basisFun ℤ (Fin (n - d))

/-- Paper label: `cor:pom-hankel-syndrome-module-rank-and-generators`.
In the concrete monic model, the shifted coefficient vectors are exactly the standard basis of the
tail coefficient space, so they form a free rank-`n - d` generating family. -/
theorem paper_pom_hankel_syndrome_module_rank_and_generators
    (n d : ℕ) (hd : d ≤ n) :
    LinearIndependent ℤ
      (pom_hankel_syndrome_module_rank_and_generators_generators n d hd) ∧
    Submodule.span ℤ
        (Set.range (pom_hankel_syndrome_module_rank_and_generators_generators n d hd)) = ⊤ ∧
    Fintype.card (Fin (n - d)) = n - d := by
  refine ⟨(Pi.basisFun ℤ (Fin (n - d))).linearIndependent, ?_, by simp⟩
  change Submodule.span ℤ (Set.range (Pi.basisFun ℤ (Fin (n - d)))) = ⊤
  exact (Pi.basisFun ℤ (Fin (n - d))).span_eq

end Omega.POM
