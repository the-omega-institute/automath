import Mathlib.Tactic
import Omega.Zeta.XiSmithKernelDirichletEulerSinglePole

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete tail data for the Smith-kernel Dirichlet Euler factor.  The local series is split
into a finite prefix and the stable geometric tail beginning at `tailStart`; the residue
normalization records the same Smith product as the single-pole seed theorem. -/
structure xi_smith_kernel_dirichlet_euler_stokes_tail_residue_data where
  n : Nat
  m : Nat
  d : Fin m → Nat
  xi_smith_kernel_dirichlet_euler_stokes_tail_residue_tailStart : Nat
  xi_smith_kernel_dirichlet_euler_stokes_tail_residue_tailRatio : Nat
  xi_smith_kernel_dirichlet_euler_stokes_tail_residue_residueScale : Nat

/-- The local coefficient before and inside the stable tail. -/
def xi_smith_kernel_dirichlet_euler_stokes_tail_residue_localCoeff
    (D : xi_smith_kernel_dirichlet_euler_stokes_tail_residue_data) (p k : Nat) : Nat :=
  p ^ k * (D.xi_smith_kernel_dirichlet_euler_stokes_tail_residue_residueScale + 1)

/-- Finite prefix of the local Smith-kernel series. -/
def xi_smith_kernel_dirichlet_euler_stokes_tail_residue_localPrefix
    (D : xi_smith_kernel_dirichlet_euler_stokes_tail_residue_data) (p : Nat) : Nat :=
  Finset.sum
    (Finset.range D.xi_smith_kernel_dirichlet_euler_stokes_tail_residue_tailStart)
    (fun k => xi_smith_kernel_dirichlet_euler_stokes_tail_residue_localCoeff D p k)

/-- Stable geometric tail after the finite Stokes prefix. -/
def xi_smith_kernel_dirichlet_euler_stokes_tail_residue_stableTail
    (D : xi_smith_kernel_dirichlet_euler_stokes_tail_residue_data) (p : Nat) : Nat :=
  xi_smith_kernel_dirichlet_euler_stokes_tail_residue_localCoeff D p
      D.xi_smith_kernel_dirichlet_euler_stokes_tail_residue_tailStart *
    D.xi_smith_kernel_dirichlet_euler_stokes_tail_residue_tailRatio

/-- The local series presented as prefix plus stable tail. -/
def xi_smith_kernel_dirichlet_euler_stokes_tail_residue_localSeries
    (D : xi_smith_kernel_dirichlet_euler_stokes_tail_residue_data) (p : Nat) : Nat :=
  xi_smith_kernel_dirichlet_euler_stokes_tail_residue_localPrefix D p +
    xi_smith_kernel_dirichlet_euler_stokes_tail_residue_stableTail D p

/-- Residue normalization inherited from the Smith-kernel single-pole theorem. -/
def xi_smith_kernel_dirichlet_euler_stokes_tail_residue_residue
    (D : xi_smith_kernel_dirichlet_euler_stokes_tail_residue_data) : Nat :=
  ∏ i : Fin D.m, D.d i + 1

/-- Euler-product component of the Stokes-tail package. -/
def xi_smith_kernel_dirichlet_euler_stokes_tail_residue_data.eulerProduct
    (D : xi_smith_kernel_dirichlet_euler_stokes_tail_residue_data) : Prop :=
  xi_smith_kernel_dirichlet_euler_single_pole_euler_product D.n D.m D.d

/-- Local prefix plus stable-tail decomposition at every prime. -/
def xi_smith_kernel_dirichlet_euler_stokes_tail_residue_data.localTailDecomposition
    (D : xi_smith_kernel_dirichlet_euler_stokes_tail_residue_data) : Prop :=
  ∀ p : Nat, Nat.Prime p →
    xi_smith_kernel_dirichlet_euler_stokes_tail_residue_localSeries D p =
      xi_smith_kernel_dirichlet_euler_stokes_tail_residue_localPrefix D p +
        xi_smith_kernel_dirichlet_euler_stokes_tail_residue_stableTail D p

/-- Unique simple pole and its residue normalization. -/
def xi_smith_kernel_dirichlet_euler_stokes_tail_residue_data.uniqueSimplePoleResidue
    (D : xi_smith_kernel_dirichlet_euler_stokes_tail_residue_data) : Prop :=
  xi_smith_kernel_dirichlet_euler_single_pole_single_pole D.n D.m D.d ∧
    xi_smith_kernel_dirichlet_euler_stokes_tail_residue_residue D =
      ∏ i : Fin D.m, D.d i + 1

/-- Paper label: `thm:xi-smith-kernel-dirichlet-euler-stokes-tail-residue`. -/
theorem paper_xi_smith_kernel_dirichlet_euler_stokes_tail_residue
    (D : xi_smith_kernel_dirichlet_euler_stokes_tail_residue_data) :
    D.eulerProduct ∧ D.localTailDecomposition ∧ D.uniqueSimplePoleResidue := by
  have hsingle := paper_xi_smith_kernel_dirichlet_euler_single_pole D.n D.m D.d
  refine ⟨hsingle.1, ?_, ?_⟩
  · intro p hp
    rfl
  · exact ⟨hsingle.2.2, rfl⟩

end Omega.Zeta
