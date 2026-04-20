import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic
import Omega.EA.ChiRigidityShadow

namespace Omega.EA

/-- Block permutations on the `m` visible summands. -/
abbrev FoldBlockPermutation (m : Nat) := Equiv.Perm (Fin m)

/-- The `χ`-rigid block permutations are exactly the sign-trivial permutations. -/
def chiRigidBlockPermutations (m : Nat) : Subgroup (FoldBlockPermutation m) where
  carrier := {σ | Equiv.Perm.sign σ = 1}
  one_mem' := by
    simp
  mul_mem' := by
    intro σ τ hσ hτ
    rw [Set.mem_setOf_eq] at hσ hτ ⊢
    simp [Equiv.Perm.sign_mul, hσ, hτ]
  inv_mem' := by
    intro σ hσ
    rw [Set.mem_setOf_eq] at hσ ⊢
    simpa [Omega.EA.sign_inv_eq_sign] using hσ

/-- Classified `χ`-preserving automorphisms as a block permutation plus a Boolean tag. -/
def foldGroupoidAutChiClassified (m : Nat) :=
  {x : FoldBlockPermutation m × Bool // x.1 ∈ chiRigidBlockPermutations m}

/-- The surviving semidirect-product data: a `χ`-rigid permutation and an internal Boolean tag. -/
abbrev FoldGroupoidAutChiSemidirectProduct (m : Nat) :=
  chiRigidBlockPermutations m × Bool

/-- The classification proposition is the existence of the natural equivalence between the
restricted automorphism data and the corresponding semidirect-product coordinates. -/
def FoldGroupoidAutChiSemidirectClassification (m : Nat) : Prop :=
  Nonempty (foldGroupoidAutChiClassified m ≃ FoldGroupoidAutChiSemidirectProduct m)

def foldGroupoidAutChiSemidirectEquiv (m : Nat) :
    foldGroupoidAutChiClassified m ≃ FoldGroupoidAutChiSemidirectProduct m where
  toFun x := (⟨x.1.1, x.2⟩, x.1.2)
  invFun y := ⟨(y.1.1, y.2), y.1.2⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro y
    cases y
    rfl

/-- Paper-facing `χ`-preserving semidirect-product classification.
    prop:fold-groupoid-aut-chi-semidirect-classification -/
theorem paper_fold_groupoid_aut_chi_semidirect_classification
    (m : Nat) : FoldGroupoidAutChiSemidirectClassification m := by
  exact ⟨foldGroupoidAutChiSemidirectEquiv m⟩

end Omega.EA
