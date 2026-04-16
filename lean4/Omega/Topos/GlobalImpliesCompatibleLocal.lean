import Mathlib.Tactic

namespace Omega.Topos

/-- Publication seed for `prop:global-implies-compatible-local`.
    A single global section restricts to a compatible local family on every chosen cover piece. -/
theorem paper_conservative_extension_global_implies_compatible_local_seeds
    {Obj Sec Glue : Type} {I : Type}
    (F : Obj → Set Sec) (piece : I → Obj) (glue : I → Sec → Glue)
    (a : Obj) (σ : Sec)
    (restrict : I → Sec → Sec)
    (hσ : σ ∈ F a)
    (hrestrict : ∀ i {τ : Sec}, τ ∈ F a → restrict i τ ∈ F (piece i))
    (hglue : ∀ i j {τ : Sec}, τ ∈ F a → glue i (restrict i τ) = glue j (restrict j τ)) :
    (∃ family : I → Sec,
      (∀ i, family i ∈ F (piece i)) ∧
      ∀ i j, glue i (family i) = glue j (family j)) ∧
    (∀ i, (F (piece i)).Nonempty) := by
  refine ⟨?_, ?_⟩
  · refine ⟨fun i => restrict i σ, ?_, ?_⟩
    · intro i
      exact hrestrict i hσ
    · intro i j
      exact hglue i j hσ
  · intro i
    exact ⟨restrict i σ, hrestrict i hσ⟩

/-- Packaged form of `prop:global-implies-compatible-local`. -/
theorem paper_conservative_extension_global_implies_compatible_local_package
    {Obj Sec Glue : Type} {I : Type}
    (F : Obj → Set Sec) (piece : I → Obj) (glue : I → Sec → Glue)
    (a : Obj) (σ : Sec)
    (restrict : I → Sec → Sec)
    (hσ : σ ∈ F a)
    (hrestrict : ∀ i {τ : Sec}, τ ∈ F a → restrict i τ ∈ F (piece i))
    (hglue : ∀ i j {τ : Sec}, τ ∈ F a → glue i (restrict i τ) = glue j (restrict j τ)) :
    (∃ family : I → Sec,
      (∀ i, family i ∈ F (piece i)) ∧
      ∀ i j, glue i (family i) = glue j (family j)) ∧
    (∀ i, (F (piece i)).Nonempty) :=
  paper_conservative_extension_global_implies_compatible_local_seeds
    F piece glue a σ restrict hσ hrestrict hglue

/-- Logic-facing wrapper for `prop:logic-expansion-global-implies-compatible-local`.
    A global section produces both a compatible local family and local nonemptiness on
    every piece of the chosen cover. -/
theorem paper_logic_expansion_global_implies_compatible_local
    {Obj Sec Glue : Type} {I : Type}
    (F : Obj → Set Sec) (piece : I → Obj) (glue : I → Sec → Glue)
    (a : Obj)
    (restrict : I → Sec → Sec)
    (hrestrict : ∀ i {τ : Sec}, τ ∈ F a → restrict i τ ∈ F (piece i))
    (hglue : ∀ i j {τ : Sec}, τ ∈ F a -> glue i (restrict i τ) = glue j (restrict j τ)) :
    (∃ σ : Sec, σ ∈ F a) →
    ((∃ family : I → Sec,
      (∀ i, family i ∈ F (piece i)) ∧
      ∀ i j, glue i (family i) = glue j (family j)) ∧
    (∀ i, (F (piece i)).Nonempty)) := by
  rintro ⟨σ, hσ⟩
  exact paper_conservative_extension_global_implies_compatible_local_package
    F piece glue a σ restrict hσ hrestrict hglue

end Omega.Topos
