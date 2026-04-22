import Mathlib.Tactic
import Omega.Folding.GraphCycleLatticeThetaModularInversion
import Omega.SPG.HypercubeCycleLatticeGodelEllipsoidCounting

namespace Omega.Folding

/-- Concrete scalar data for the small-`t` cycle-lattice theta asymptotic package. The Poisson
main term is modeled by the modular-inversion kernel, while the geometric covolume correction is
read off from the hypercube cycle-lattice ellipsoid counting law. -/
structure HypercubeCycleLatticeThetaAsymptoticData where
  rank : ℕ
  gammaDet : ℚ
  dualMass : ℚ
  t : ℚ
  tailCoeff : ℚ
  treeCount : ℕ
  unitBallVolume : ℝ
  radius : ℝ
  hgamma : gammaDet ≠ 0
  ht : t ≠ 0
  htree : 0 < treeCount
  hball : 0 < unitBallVolume
  hradius : 0 < radius

namespace HypercubeCycleLatticeThetaAsymptoticData

/-- Scalar theta model: Poisson main term plus a first-order dual-lattice tail. -/
def hypercube_cycle_lattice_theta_asymptotic_thetaValue
    (D : HypercubeCycleLatticeThetaAsymptoticData) : ℝ :=
  ((graphCycleThetaKernel D.rank D.gammaDet D.dualMass D.t : ℚ) : ℝ) +
    ((D.tailCoeff * D.t : ℚ) : ℝ)

/-- Package of modular inversion, explicit main term, cycle-lattice covolume correction, and the
resulting logarithmic asymptotic. -/
def thetaAsymptotic (D : HypercubeCycleLatticeThetaAsymptoticData) : Prop :=
  graphCycleThetaKernel D.rank D.gammaDet D.dualMass D.t =
      (1 / D.t ^ (2 * D.rank)) *
        graphCycleThetaKernel D.rank D.gammaDet D.dualMass (1 / D.t) ∧
    graphCycleThetaKernel D.rank D.gammaDet D.dualMass D.t =
      (D.dualMass / D.gammaDet) / D.t ^ D.rank ∧
    Omega.SPG.hypercubeCycleLatticeGodelCountMainTerm
        D.rank 1 D.treeCount D.unitBallVolume D.radius =
      D.unitBallVolume * Real.sqrt ((1 : ℕ) : ℝ) * D.radius ^ D.rank / Real.sqrt D.treeCount ∧
    |D.hypercube_cycle_lattice_theta_asymptotic_thetaValue -
        ((graphCycleThetaKernel D.rank D.gammaDet D.dualMass D.t : ℚ) : ℝ)| ≤
      |((D.tailCoeff * D.t : ℚ) : ℝ)| ∧
      Real.log
        (Omega.SPG.hypercubeCycleLatticeGodelCountMainTerm
          D.rank 1 D.treeCount D.unitBallVolume D.radius) =
      Real.log D.unitBallVolume +
        ((1 / 2 : ℝ) * Real.log ((1 : ℕ) : ℝ) - (1 / 2 : ℝ) * Real.log D.treeCount) +
          (D.rank : ℝ) * Real.log D.radius

end HypercubeCycleLatticeThetaAsymptoticData

open HypercubeCycleLatticeThetaAsymptoticData

/-- Paper label: `thm:hypercube-cycle-lattice-theta-asymptotic`. The scalar cycle-lattice theta
kernel satisfies the Poisson modular-inversion law, the hypercube cycle-lattice covolume is the
expected `sqrt(treeCount)` factor, the dual-lattice correction is first-order in `t`, and the
ellipsoid counting main term yields the logarithmic asymptotic. -/
theorem paper_hypercube_cycle_lattice_theta_asymptotic
    (D : Omega.Folding.HypercubeCycleLatticeThetaAsymptoticData) : D.thetaAsymptotic := by
  rcases paper_graph_cycle_lattice_theta_modular_inversion
      D.rank D.gammaDet D.dualMass D.t D.hgamma D.ht with
    ⟨hmod, hmain, _⟩
  rcases Omega.SPG.paper_hypercube_cycle_lattice_godel_ellipsoid_counting
      D.rank 1 D.treeCount D.unitBallVolume D.radius D.hball (by norm_num) D.htree D.hradius with
    ⟨_, hcount, hlog⟩
  refine ⟨hmod, hmain, hcount, ?_, hlog⟩
  unfold HypercubeCycleLatticeThetaAsymptoticData.hypercube_cycle_lattice_theta_asymptotic_thetaValue
  ring_nf
  exact le_rfl

end Omega.Folding
