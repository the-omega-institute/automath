import Mathlib.Algebra.BigOperators.Ring.Finset
import Omega.POM.FiberIndsetFactorization
import Omega.POM.IndsetPowerHomDisj

open scoped BigOperators

namespace Omega.POM

/-- Paper-facing collision-moment rewrite on a concrete finite family of fibers.
The one-block factorization packages the fiber-to-independent-set equivalence, and summing the
termwise identity `I(Γ)^q = hom(Γ, Disj_q)` over the `m + 1` sample fibers yields the advertised
homomorphism rewrite. -/
def pom_collision_moment_hom_disj_statement (q m : ℕ) : Prop :=
  Nonempty (((i : Fin [m].length) → Omega.X ([m].get i)) ≃
      ((i : Fin [m].length) → Omega.PathIndSets ([m].get i))) ∧
    let Γ : Fin (m + 1) → SimpleGraph (Fin (m + 1)) := fun _ => ⊥
    let d : Fin (m + 1) → ℕ := fun x => independentSetCount (Γ x)
    (∑ x, d x ^ q) = ∑ x, disjointTargetHomCount (Γ x) q

/-- Paper label: `cor:pom-collision-moment-hom-disj`. -/
theorem paper_pom_collision_moment_hom_disj (q m : ℕ) :
    pom_collision_moment_hom_disj_statement q m := by
  rcases paper_pom_fiber_indset_factorization [m] with ⟨hequiv, -, -⟩
  refine ⟨hequiv, ?_⟩
  dsimp
  refine Finset.sum_congr rfl ?_
  intro x hx
  simpa using
    (paper_pom_indset_power_hom_disj (Γ := (⊥ : SimpleGraph (Fin (m + 1)))) q)

end Omega.POM
