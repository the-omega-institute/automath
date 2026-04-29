import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:conclusion-firstfit-no-recursive-uniform-proof-bound`. -/
theorem paper_conclusion_firstfit_no_recursive_uniform_proof_bound
    (Word Cert : Type) (size : Word → Nat) (mom : Nat → Word → Word)
    (equivExt : Word → Word → Prop) (certifies : Cert → Word → Word → Prop)
    (certLength : Cert → Nat)
    (hbounded_decides :
      (∃ F : Nat → Nat → Nat,
        ∀ u v q,
          equivExt (mom q u) (mom q v) →
            ∃ c,
              certifies c (mom q u) (mom q v) ∧
                certLength c ≤ F (max (size u) (size v)) q) →
        ∃ decideEquiv : Word → Word → Bool,
          ∀ u v, decideEquiv u v = true ↔ equivExt u v)
    (hundecidable :
      ¬ ∃ decideEquiv : Word → Word → Bool,
        ∀ u v, decideEquiv u v = true ↔ equivExt u v) :
    ¬ ∃ F : Nat → Nat → Nat,
      ∀ u v q,
        equivExt (mom q u) (mom q v) →
          ∃ c,
            certifies c (mom q u) (mom q v) ∧
              certLength c ≤ F (max (size u) (size v)) q := by
  intro hF
  exact hundecidable (hbounded_decides hF)

end Omega.POM
