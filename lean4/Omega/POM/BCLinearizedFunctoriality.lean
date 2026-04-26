import Mathlib.Tactic
import Omega.POM.BCBianchi
import Omega.POM.BCDiscreteStokes
import Omega.POM.BCUniformLiftPseudofunctor

namespace Omega.POM

noncomputable section

/-- The linearized uniform lift acts on finite test functions by pullback. -/
def pom_bc_linearized_functoriality_uniformLift {X Y : Type*} (f : X → Y) (φ : Y → ℝ) : X → ℝ :=
  fun x => φ (f x)

/-- The base linearization stage keeps the finite observable unchanged on the middle layer. -/
def pom_bc_linearized_functoriality_linearLift {X Y : Type*} (_f : X → Y) (φ : Y → ℝ) : Y → ℝ :=
  φ

/-- The diagonal correction stage is again the pullback along `f`. -/
def pom_bc_linearized_functoriality_diagonalLift {X Y : Type*} (f : X → Y) (ψ : Y → ℝ) : X → ℝ :=
  fun x => ψ (f x)

lemma pom_bc_linearized_functoriality_uniformLift_comp {X Y Z : Type*} (f : X → Y) (g : Y → Z)
    (φ : Z → ℝ) :
    pom_bc_linearized_functoriality_uniformLift f
        (pom_bc_linearized_functoriality_uniformLift g φ) =
      pom_bc_linearized_functoriality_uniformLift (g ∘ f) φ := by
  funext x
  rfl

lemma pom_bc_linearized_functoriality_uniformLift_factor {X Y : Type*} (f : X → Y) :
    pom_bc_linearized_functoriality_uniformLift f =
      pom_bc_linearized_functoriality_diagonalLift f ∘
        pom_bc_linearized_functoriality_linearLift f := by
  funext φ
  funext x
  rfl

/-- Paper label: `prop:pom-bc-linearized-functoriality`. On finite observable spaces the
linearized uniform lift is strictly functorial by extensionality, it factors as diagonal
correction after the trivial linear lift, and the existing Beck--Chevalley pseudofunctor,
Bianchi, and discrete-Stokes packages supply the flatness consequences. -/
theorem paper_pom_bc_linearized_functoriality {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq Y] [DecidableEq Z] (f : X → Y) (g : Y → Z) :
    (∀ φ : Z → ℝ,
      pom_bc_linearized_functoriality_uniformLift f
          (pom_bc_linearized_functoriality_uniformLift g φ) =
        pom_bc_linearized_functoriality_uniformLift (g ∘ f) φ) ∧
      pom_bc_linearized_functoriality_uniformLift f =
        pom_bc_linearized_functoriality_diagonalLift f ∘
          pom_bc_linearized_functoriality_linearLift f ∧
      (bcPentagonCoherence (Fintype.card X) (Fintype.card Y) (Fintype.card Z) ∧
        bcLogCocycleClosed (Fintype.card X) (Fintype.card Y) (Fintype.card Z)) ∧
      (∀ x : X,
        pom_bc_bianchi_curvature f g x = -pom_bc_bianchi_coboundary f g x ∧
          pom_bc_bianchi_curvature g id (f x) -
              pom_bc_bianchi_curvature (g ∘ f) id x +
              pom_bc_bianchi_curvature f (id ∘ g) x -
              pom_bc_bianchi_curvature f g x = 0) ∧
      (∀ C : BCDiscreteStokesComplex, paper_pom_bc_discrete_stokes_statement C) := by
  refine ⟨?_, pom_bc_linearized_functoriality_uniformLift_factor f, ?_, ?_, ?_⟩
  · intro φ
    exact pom_bc_linearized_functoriality_uniformLift_comp f g φ
  · exact paper_pom_bc_uniform_lift_pseudofunctor (Fintype.card X) (Fintype.card Y) (Fintype.card Z)
  · intro x
    simpa [Function.comp] using paper_pom_bc_bianchi f g id x
  · intro C
    exact paper_pom_bc_discrete_stokes C

end

end Omega.POM
