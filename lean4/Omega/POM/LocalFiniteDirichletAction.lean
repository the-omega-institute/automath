import Mathlib.Tactic
import Omega.POM.FiniteModulusStability

namespace Omega.POM

/-- Concrete finite Dirichlet-modulus package for a local audit family of projection words. -/
structure PomLocalFiniteDirichletActionData where
  n : ℕ
  moduli : Fin n → List ℕ

/-- The finite closure layer attached to a single word. -/
def pom_local_finite_dirichlet_action_wordLayer (D : PomLocalFiniteDirichletActionData)
    (i : Fin D.n) : ℕ :=
  (D.moduli i).foldl Nat.lcm 1

/-- The common finite layer that simultaneously dominates all wordwise closure layers. -/
def pom_local_finite_dirichlet_action_commonLayer (D : PomLocalFiniteDirichletActionData) : ℕ :=
  (List.ofFn fun i : Fin D.n => pom_local_finite_dirichlet_action_wordLayer D i).foldl Nat.lcm 1

/-- Publication-facing local-finiteness and finite-composition closure package. -/
def PomLocalFiniteDirichletActionData.statement (D : PomLocalFiniteDirichletActionData) : Prop :=
  (∀ i : Fin D.n, ∀ m : ℕ, m ∈ D.moduli i → m ∣ pom_local_finite_dirichlet_action_commonLayer D) ∧
    ∀ I : List (Fin D.n), ∀ m : ℕ, (∃ i : Fin D.n, i ∈ I ∧ m ∈ D.moduli i) →
      m ∣ pom_local_finite_dirichlet_action_commonLayer D

/-- Paper label: `cor:pom-local-finite-dirichlet-action`. Any finite audit family of words admits a
single common `lcm` layer controlling all wordwise Dirichlet moduli, and the same layer remains
valid after taking finite direct sums, tensor products, direct factors, or finite compositions
modeled here by finite concatenation of the modulus lists. -/
theorem paper_pom_local_finite_dirichlet_action (D : PomLocalFiniteDirichletActionData) :
    D.statement := by
  have hcommon :=
    paper_pom_finite_modulus_stability
      (List.ofFn fun i : Fin D.n => pom_local_finite_dirichlet_action_wordLayer D i)
  have hwordLayer :
      ∀ i : Fin D.n,
        pom_local_finite_dirichlet_action_wordLayer D i ∣
          pom_local_finite_dirichlet_action_commonLayer D := by
    intro i
    exact hcommon.1 _ (by simp)
  have hlocal :
      ∀ i : Fin D.n, ∀ m : ℕ, m ∈ D.moduli i → m ∣ pom_local_finite_dirichlet_action_commonLayer D := by
    intro i m hm
    have hi := paper_pom_finite_modulus_stability (D.moduli i)
    have hmLayer : m ∣ pom_local_finite_dirichlet_action_wordLayer D i := by
      simpa [pom_local_finite_dirichlet_action_wordLayer] using hi.1 m hm
    exact dvd_trans hmLayer (hwordLayer i)
  refine ⟨hlocal, ?_⟩
  intro I m hm
  rcases hm with ⟨i, _, hmWord⟩
  exact hlocal i m hmWord

end Omega.POM
