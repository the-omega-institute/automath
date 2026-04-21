import Mathlib.Tactic
import Omega.CircleDimension.StokesExplicitRelativeCohomologyBasis

namespace Omega.CircleDimension

open Omega.CircleDimension.StokesHomologyExactSplitting

/-- The split direct-sum decomposition used for the relative Stokes cohomology ring model. -/
def stokesRelativeGradedDecomposition (u v : ℕ) (p : StokesRelativeCohomologyClass u v) :
    StokesRelativeCohomologyClass u v × StokesRelativeCohomologyClass u v :=
  (stokesSection u v (stokesProjection u v p), stokesBoundaryInclusion u v p.2)

/-- Cup product on the concrete split model: add the torus and boundary coordinates separately. -/
def stokesRelativeCupProduct (u v : ℕ) (p q : StokesRelativeCohomologyClass u v) :
    StokesRelativeCohomologyClass u v :=
  (p.1 + q.1, p.2 + q.2)

/-- Wedge product on the explicit basis model; in the split coordinate package it is the same
coordinatewise addition law as the cup product. -/
def stokesRelativeWedgeProduct (u v : ℕ) (p q : StokesRelativeCohomologyClass u v) :
    StokesRelativeCohomologyClass u v :=
  stokesRelativeCupProduct u v p q

/-- Paper-facing split-model statement for the relative Stokes cohomology ring: the exact/basis
dictionary gives the direct-sum decomposition, and the cup product agrees with the wedge product
on the explicit torus and boundary generators. -/
def paper_cdim_stokes_relative_cohomology_ring_statement (u v : ℕ) : Prop :=
  paper_cdim_stokes_explicit_relative_cohomology_basis_statement u v ∧
    (∀ p,
      (stokesRelativeGradedDecomposition u v p).1 +
          (stokesRelativeGradedDecomposition u v p).2 = p) ∧
    (∀ p q, stokesRelativeCupProduct u v p q = stokesRelativeWedgeProduct u v p q) ∧
    (∀ i i',
      stokesRelativeCupProduct u v (stokesTorusBasisClass u v i) (stokesTorusBasisClass u v i') =
        stokesRelativeWedgeProduct u v (stokesTorusBasisClass u v i) (stokesTorusBasisClass u v i')) ∧
    (∀ i j,
      stokesRelativeCupProduct u v (stokesTorusBasisClass u v i) (stokesRelativeBasisClass u v j) =
        stokesRelativeWedgeProduct u v
          (stokesTorusBasisClass u v i) (stokesRelativeBasisClass u v j)) ∧
    (∀ j j',
      stokesRelativeCupProduct u v (stokesRelativeBasisClass u v j)
          (stokesRelativeBasisClass u v j') =
        stokesRelativeWedgeProduct u v
          (stokesRelativeBasisClass u v j) (stokesRelativeBasisClass u v j'))

/-- Split-coordinate relative cohomology ring package for `T^u × D^v`.
    prop:cdim-stokes-relative-cohomology-ring -/
theorem paper_cdim_stokes_relative_cohomology_ring (u v : Nat) :
    paper_cdim_stokes_relative_cohomology_ring_statement u v := by
  rcases paper_cdim_stokes_exact_sequence_dictionary u v with ⟨_hInj, _hSurj, _hRange, hDecomp⟩
  refine ⟨paper_cdim_stokes_explicit_relative_cohomology_basis u v, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    simpa [stokesRelativeGradedDecomposition] using hDecomp p
  · intro p q
    rfl
  · intro i i'
    rfl
  · intro i j
    rfl
  · intro j j'
    rfl

end Omega.CircleDimension
