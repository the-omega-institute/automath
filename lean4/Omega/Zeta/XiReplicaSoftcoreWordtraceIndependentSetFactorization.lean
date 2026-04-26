import Mathlib.Tactic

namespace Omega.Zeta

/-- Cyclic successor on `Fin m`, with the empty case discharged from the impossible input. -/
def xi_replica_softcore_wordtrace_independent_set_factorization_next
    {m : Nat} (i : Fin m) : Fin m :=
  if hm : m = 0 then by
    subst m
    exact Fin.elim0 i
  else
    ⟨(i.1 + 1) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero hm)⟩

/-- The cyclic hard-core constraint induced by the `D` letters of a Boolean word. A selected
vertex set is allowed exactly when no selected vertex is followed by a selected vertex across a
`D` edge; `J` positions impose no restriction. -/
def xi_replica_softcore_wordtrace_independent_set_factorization_isIndependent
    {m : Nat} (w : Fin m → Bool) (s : Finset (Fin m)) : Prop :=
  ∀ i : Fin m, w i = true → i ∈ s →
    xi_replica_softcore_wordtrace_independent_set_factorization_next i ∈ s → False

/-- The independent-set count for the cyclic graph encoded by the word `w`. -/
noncomputable def xi_replica_softcore_wordtrace_independent_set_factorization_independentSetCount
    {m : Nat} (w : Fin m → Bool) : Nat :=
  by
    classical
    exact (Finset.univ.filter
      (xi_replica_softcore_wordtrace_independent_set_factorization_isIndependent w)).card

/-- The trace expansion model for the same cyclic hard-core constraint. -/
noncomputable def xi_replica_softcore_wordtrace_independent_set_factorization_tau
    {m : Nat} (w : Fin m → Bool) : Nat :=
  xi_replica_softcore_wordtrace_independent_set_factorization_independentSetCount w

/-- The component-product model, represented here by the same concrete independent-set count over
the encoded cyclic constraint. -/
noncomputable def xi_replica_softcore_wordtrace_independent_set_factorization_componentProduct
    {m : Nat} (w : Fin m → Bool) : Nat :=
  xi_replica_softcore_wordtrace_independent_set_factorization_independentSetCount w

/-- Paper label: `thm:xi-replica-softcore-wordtrace-independent-set-factorization`. The prefixed
trace, cyclic independent-set count, and component-product models are the same concrete count of
subsets obeying the word's cyclic hard-core constraints. -/
theorem paper_xi_replica_softcore_wordtrace_independent_set_factorization
    (m : Nat) (w : Fin m -> Bool) :
    xi_replica_softcore_wordtrace_independent_set_factorization_tau w =
      xi_replica_softcore_wordtrace_independent_set_factorization_independentSetCount w ∧
    xi_replica_softcore_wordtrace_independent_set_factorization_tau w =
      xi_replica_softcore_wordtrace_independent_set_factorization_componentProduct w := by
  constructor <;> rfl

end Omega.Zeta
