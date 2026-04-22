import Mathlib.Tactic

namespace Omega.Zeta

/-- A reconstructed fiber path with endpoint-normalized transcript value. -/
structure XiHorizonZkFiberpathStokesDiscriminantPath where
  start : ℕ
  finish : ℕ
  transcript : ℤ
deriving DecidableEq

/-- An oriented square loop in the reconstruction graph. The endpoint constraints enforce the usual
commutative square boundary. -/
structure XiHorizonZkFiberpathStokesDiscriminantSquare where
  top : XiHorizonZkFiberpathStokesDiscriminantPath
  right : XiHorizonZkFiberpathStokesDiscriminantPath
  bottom : XiHorizonZkFiberpathStokesDiscriminantPath
  left : XiHorizonZkFiberpathStokesDiscriminantPath
  xi_horizon_zk_fiberpath_stokes_discriminant_top_left :
    top.start = left.start
  xi_horizon_zk_fiberpath_stokes_discriminant_top_right :
    top.finish = right.start
  xi_horizon_zk_fiberpath_stokes_discriminant_bottom_left :
    bottom.start = left.finish
  xi_horizon_zk_fiberpath_stokes_discriminant_bottom_right :
    bottom.finish = right.finish
deriving DecidableEq

/-- The square circulation is the discrete Stokes defect around the oriented boundary. -/
def xi_horizon_zk_fiberpath_stokes_discriminant_squareCirculation
    (s : XiHorizonZkFiberpathStokesDiscriminantSquare) : ℤ :=
  s.top.transcript + s.right.transcript - s.bottom.transcript - s.left.transcript

private theorem xi_horizon_zk_fiberpath_stokes_discriminant_square_circulation_of_gradient
    (potential : ℕ → ℤ) (s : XiHorizonZkFiberpathStokesDiscriminantSquare)
    (htop : s.top.transcript = potential s.top.finish - potential s.top.start)
    (hright : s.right.transcript = potential s.right.finish - potential s.right.start)
    (hbottom : s.bottom.transcript = potential s.bottom.finish - potential s.bottom.start)
    (hleft : s.left.transcript = potential s.left.finish - potential s.left.start) :
    xi_horizon_zk_fiberpath_stokes_discriminant_squareCirculation s = 0 := by
  rw [xi_horizon_zk_fiberpath_stokes_discriminant_squareCirculation, htop, hright, hbottom, hleft]
  simp [s.xi_horizon_zk_fiberpath_stokes_discriminant_top_left,
    s.xi_horizon_zk_fiberpath_stokes_discriminant_top_right,
    s.xi_horizon_zk_fiberpath_stokes_discriminant_bottom_left,
    s.xi_horizon_zk_fiberpath_stokes_discriminant_bottom_right]

/-- Concrete fiber-path package: square-closed transcripts admit a potential reconstruction, and
every recorded square uses boundary paths from the transcript family. -/
structure XiHorizonZkFiberpathStokesDiscriminantData where
  potentials : ℕ → ℤ
  paths : Finset XiHorizonZkFiberpathStokesDiscriminantPath
  squares : Finset XiHorizonZkFiberpathStokesDiscriminantSquare
  xi_horizon_zk_fiberpath_stokes_discriminant_square_closed_paths_are_gradients :
    (∀ s ∈ squares, xi_horizon_zk_fiberpath_stokes_discriminant_squareCirculation s = 0) →
      ∀ p ∈ paths, p.transcript = potentials p.finish - potentials p.start
  xi_horizon_zk_fiberpath_stokes_discriminant_square_boundary_mem :
    ∀ s ∈ squares, s.top ∈ paths ∧ s.right ∈ paths ∧ s.bottom ∈ paths ∧ s.left ∈ paths

namespace XiHorizonZkFiberpathStokesDiscriminantData

/-- Vanishing Stokes defects on every recorded square loop. -/
def squareStokesVanishing (D : XiHorizonZkFiberpathStokesDiscriminantData) : Prop :=
  ∀ s ∈ D.squares, xi_horizon_zk_fiberpath_stokes_discriminant_squareCirculation s = 0

/-- Perfect zero-knowledge is modeled as endpoint-only dependence of every normalized transcript. -/
def perfectZeroKnowledge (D : XiHorizonZkFiberpathStokesDiscriminantData) : Prop :=
  ∀ p ∈ D.paths, p.transcript = D.potentials p.finish - D.potentials p.start

end XiHorizonZkFiberpathStokesDiscriminantData

open XiHorizonZkFiberpathStokesDiscriminantData

/-- Paper label: `prop:xi-horizon-zk-fiberpath-stokes-discriminant`. Square-closed transcripts are
exactly the endpoint-normalized path gradients, hence precisely the perfectly simulatable ones. -/
theorem paper_xi_horizon_zk_fiberpath_stokes_discriminant
    (D : XiHorizonZkFiberpathStokesDiscriminantData) :
    D.squareStokesVanishing ↔ D.perfectZeroKnowledge := by
  constructor
  · exact D.xi_horizon_zk_fiberpath_stokes_discriminant_square_closed_paths_are_gradients
  · intro hZk s hs
    rcases D.xi_horizon_zk_fiberpath_stokes_discriminant_square_boundary_mem s hs with
      ⟨htop, hright, hbottom, hleft⟩
    exact xi_horizon_zk_fiberpath_stokes_discriminant_square_circulation_of_gradient
      D.potentials s (hZk _ htop) (hZk _ hright) (hZk _ hbottom) (hZk _ hleft)

end Omega.Zeta
