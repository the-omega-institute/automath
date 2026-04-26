import Mathlib.Tactic

namespace Omega.POM

/-- Equality of the signature and spectral semantics on a bounded slice yields both the
algorithmic-equivalence certificate and the induced invertible 2-morphism.
    thm:pom-sem-conservative-on-slice -/
theorem paper_pom_sem_conservative_on_slice {alpha sigma tau : Type*}
    (SemSig : alpha → sigma) (SemSpec : alpha → tau) (iso algEq : alpha → alpha → Prop)
    (hSem : ∀ {w1 w2}, SemSig w1 = SemSig w2 → SemSpec w1 = SemSpec w2 → algEq w1 w2)
    (hIso : ∀ {w1 w2}, algEq w1 w2 → iso w1 w2) :
    ∀ {w1 w2}, SemSig w1 = SemSig w2 → SemSpec w1 = SemSpec w2 → iso w1 w2 ∧ algEq w1 w2 := by
  intro w1 w2 hSig hSpec
  have hAlg : algEq w1 w2 := hSem hSig hSpec
  exact ⟨hIso hAlg, hAlg⟩

/-- Paper label: `thm:pom-sem-conservative`. The bounded-slice conservative theorem already
returns both the natural-isomorphism witness and the algorithmic-equivalence certificate; the
paper-facing statement projects out the natural-isomorphism component. -/
theorem paper_pom_sem_conservative {alpha sigma tau : Type*}
    (SemSig : alpha → sigma) (SemSpec : alpha → tau) (iso algEq : alpha → alpha → Prop)
    (hSem : ∀ {w1 w2}, SemSig w1 = SemSig w2 → SemSpec w1 = SemSpec w2 → algEq w1 w2)
    (hIso : ∀ {w1 w2}, algEq w1 w2 → iso w1 w2) :
    ∀ {w1 w2}, SemSig w1 = SemSig w2 → SemSpec w1 = SemSpec w2 → iso w1 w2 := by
  intro w1 w2 hSig hSpec
  exact
    (paper_pom_sem_conservative_on_slice SemSig SemSpec iso algEq hSem hIso hSig hSpec).1

end Omega.POM
