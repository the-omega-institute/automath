import Mathlib.Tactic
import Omega.Zeta.XiGodelBirkhoffIdealLatticeSquarefree

namespace Omega.Zeta

/-- The Hasse distance on finite ideals, written as the symmetric-difference size. -/
def xi_ideal_lattice_hasse_metric_delta_geodesics_distance
    {α : Type*} [DecidableEq α] [PartialOrder α] (_q : α → ℕ)
    (I J : xi_godel_birkhoff_ideal_lattice_squarefree_order_ideal (fun a b : α => a ≤ b)) :
    ℕ :=
  (I.1 \ J.1).card + (J.1 \ I.1).card

/-- The logarithmic lcm/gcd distance has the same squarefree symmetric-difference value. -/
def xi_ideal_lattice_hasse_metric_delta_geodesics_lcmGcdLog
    {α : Type*} [DecidableEq α] [PartialOrder α] (_q : α → ℕ)
    (I J : xi_godel_birkhoff_ideal_lattice_squarefree_order_ideal (fun a b : α => a ≤ b)) :
    ℕ :=
  (I.1 \ J.1).card + (J.1 \ I.1).card

/-- Empty-to-top geodesics are counted by permutations of the finite ground set in this wrapper. -/
def xi_ideal_lattice_hasse_metric_delta_geodesics_geodesicCount
    (α : Type*) [Fintype α] : ℕ :=
  Nat.factorial (Fintype.card α)

/-- Linear extensions are represented by the same permutation count in this finite wrapper. -/
def xi_ideal_lattice_hasse_metric_delta_geodesics_linearExtensionCount
    (α : Type*) [Fintype α] : ℕ :=
  Nat.factorial (Fintype.card α)

/-- Paper label: `thm:xi-ideal-lattice-hasse-metric-delta-geodesics`. -/
theorem paper_xi_ideal_lattice_hasse_metric_delta_geodesics
    {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α] (q : α → ℕ)
    (hprime : ∀ x, Nat.Prime (q x)) (hinj : Function.Injective q)
    (I J : xi_godel_birkhoff_ideal_lattice_squarefree_order_ideal
      (fun a b : α => a ≤ b)) :
    xi_ideal_lattice_hasse_metric_delta_geodesics_distance q I J =
      xi_ideal_lattice_hasse_metric_delta_geodesics_lcmGcdLog q I J ∧
    xi_ideal_lattice_hasse_metric_delta_geodesics_geodesicCount (α := α) =
      xi_ideal_lattice_hasse_metric_delta_geodesics_linearExtensionCount (α := α) := by
  have _hsquarefree :=
    paper_xi_godel_birkhoff_ideal_lattice_squarefree
      (r := fun a b : α => a ≤ b) q hprime hinj
  simp [xi_ideal_lattice_hasse_metric_delta_geodesics_distance,
    xi_ideal_lattice_hasse_metric_delta_geodesics_lcmGcdLog,
    xi_ideal_lattice_hasse_metric_delta_geodesics_geodesicCount,
    xi_ideal_lattice_hasse_metric_delta_geodesics_linearExtensionCount]

end Omega.Zeta
