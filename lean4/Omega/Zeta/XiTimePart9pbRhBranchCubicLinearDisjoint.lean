import Mathlib.Tactic

namespace Omega.Zeta

/-- Triviality of the intersection degree over the rational base. -/
def xi_time_part9pb_rh_branch_cubic_linear_disjoint_trivialIntersection
    (intersectionDegree : Nat) : Prop :=
  intersectionDegree = 1

/-- The finite-degree compositum predicted by the tower formula. -/
def xi_time_part9pb_rh_branch_cubic_linear_disjoint_compositumDegree
    (cubicDegree rhDegree intersectionDegree : Nat) : Nat :=
  cubicDegree * rhDegree / intersectionDegree

/-- The cubic and quintic branches have degree-fifteen compositum. -/
def xi_time_part9pb_rh_branch_cubic_linear_disjoint_compositumDegreeFifteen
    (cubicDegree rhDegree intersectionDegree : Nat) : Prop :=
  xi_time_part9pb_rh_branch_cubic_linear_disjoint_compositumDegree
    cubicDegree rhDegree intersectionDegree = 15

/-- Concrete linear-disjointness certificate carried by the degree computation. -/
def xi_time_part9pb_rh_branch_cubic_linear_disjoint_linearDisjoint
    (cubicDegree rhDegree intersectionDegree : Nat) : Prop :=
  xi_time_part9pb_rh_branch_cubic_linear_disjoint_trivialIntersection intersectionDegree ∧
    xi_time_part9pb_rh_branch_cubic_linear_disjoint_compositumDegreeFifteen
      cubicDegree rhDegree intersectionDegree

/-- Paper label: `thm:xi-time-part9pb-rh-branch-cubic-linear-disjoint`.
If the branch field has degree `3`, the RH field has degree `5`, and the intersection degree
divides both, then the intersection is the base field, the compositum degree is `15`, and the
two extensions are linearly disjoint in this finite-degree certificate sense. -/
theorem paper_xi_time_part9pb_rh_branch_cubic_linear_disjoint
    (cubicDegree rhDegree intersectionDegree : Nat)
    (hcubic : cubicDegree = 3) (hrh : rhDegree = 5)
    (hintersection_cubic : intersectionDegree ∣ cubicDegree)
    (hintersection_rh : intersectionDegree ∣ rhDegree) :
    xi_time_part9pb_rh_branch_cubic_linear_disjoint_trivialIntersection intersectionDegree ∧
      xi_time_part9pb_rh_branch_cubic_linear_disjoint_compositumDegreeFifteen
        cubicDegree rhDegree intersectionDegree ∧
        xi_time_part9pb_rh_branch_cubic_linear_disjoint_linearDisjoint
          cubicDegree rhDegree intersectionDegree := by
  have hdiv3 : intersectionDegree ∣ 3 := by
    simpa [hcubic] using hintersection_cubic
  have hdiv5 : intersectionDegree ∣ 5 := by
    simpa [hrh] using hintersection_rh
  have hintersection : intersectionDegree = 1 := by
    exact Nat.dvd_one.mp (by simpa using Nat.dvd_gcd hdiv3 hdiv5)
  have hdegree :
      xi_time_part9pb_rh_branch_cubic_linear_disjoint_compositumDegreeFifteen
        cubicDegree rhDegree intersectionDegree := by
    simp [xi_time_part9pb_rh_branch_cubic_linear_disjoint_compositumDegreeFifteen,
      xi_time_part9pb_rh_branch_cubic_linear_disjoint_compositumDegree, hcubic, hrh,
      hintersection]
  exact ⟨hintersection, hdegree, hintersection, hdegree⟩

end Omega.Zeta
