import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Fiber cardinality of a finite map over a chosen codomain point. -/
def pom_bc_bianchi_fiber_card {X Y : Type*} [Fintype X] [DecidableEq Y] (f : X → Y) (y : Y) :
    ℕ :=
  Fintype.card {x : X // f x = y}

/-- The concrete Beck--Chevalley potential given by the logarithmic fiber size. -/
def pom_bc_bianchi_potential {X Y : Type*} [Fintype X] [DecidableEq Y] (f : X → Y) (x : X) : ℝ :=
  Real.log (pom_bc_bianchi_fiber_card f (f x))

/-- The concrete curvature attached to a composable pair, written so it is visibly the negative
of the simplicial coboundary of the potential. -/
def pom_bc_bianchi_curvature {X Y Z : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    [DecidableEq Z] (f : X → Y) (g : Y → Z) (x : X) : ℝ :=
  pom_bc_bianchi_potential (g ∘ f) x -
    pom_bc_bianchi_potential g (f x) -
    pom_bc_bianchi_potential f x

/-- The simplicial coboundary of the concrete fiber potential. -/
def pom_bc_bianchi_coboundary {X Y Z : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    [DecidableEq Z] (f : X → Y) (g : Y → Z) (x : X) : ℝ :=
  pom_bc_bianchi_potential g (f x) +
    pom_bc_bianchi_potential f x -
    pom_bc_bianchi_potential (g ∘ f) x

/-- Paper label: `prop:pom-bc-bianchi`. -/
theorem paper_pom_bc_bianchi {X Y Z W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq Y] [DecidableEq Z] [DecidableEq W]
    (f : X → Y) (g : Y → Z) (h : Z → W) (x : X) :
    pom_bc_bianchi_curvature f g x = -pom_bc_bianchi_coboundary f g x ∧
      pom_bc_bianchi_curvature g h (f x) -
          pom_bc_bianchi_curvature (g ∘ f) h x +
          pom_bc_bianchi_curvature f (h ∘ g) x -
          pom_bc_bianchi_curvature f g x = 0 := by
  constructor
  · unfold pom_bc_bianchi_curvature pom_bc_bianchi_coboundary
    ring
  · unfold pom_bc_bianchi_curvature pom_bc_bianchi_potential
    simp [Function.comp]
    have hassoc :
        pom_bc_bianchi_fiber_card (h ∘ g ∘ f) (h (g (f x))) =
          pom_bc_bianchi_fiber_card ((h ∘ g) ∘ f) (h (g (f x))) := by
      rfl
    rw [hassoc]
    ring_nf

end

end Omega.POM
