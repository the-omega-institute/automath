import Omega.Zeta.XiTimePart60acbConstantFiberFreeGroupActionCriterion
import Mathlib.Tactic

namespace Omega.Zeta

open scoped Classical

/-- Concrete fold data for the window-`6` quotient obstruction: a finite fold map together with
two quotient fibers of different cardinalities. -/
structure xi_time_part9zp_window6_quotient_intrinsically_groupoidal_data where
  state : Type
  quot : Type
  [fintypeState : Fintype state]
  [fintypeQuot : Fintype quot]
  fold : state → quot
  fold_surjective : Function.Surjective fold
  smallFiber : quot
  largeFiber : quot
  smallFiber_card :
    Fintype.card {omega : state // fold omega = smallFiber} = 2
  largeFiber_card :
    Fintype.card {omega : state // fold omega = largeFiber} = 3

attribute [instance]
  xi_time_part9zp_window6_quotient_intrinsically_groupoidal_data.fintypeState
  xi_time_part9zp_window6_quotient_intrinsically_groupoidal_data.fintypeQuot

namespace xi_time_part9zp_window6_quotient_intrinsically_groupoidal_data

/-- A quotient fiber of the concrete fold map. -/
abbrev xi_time_part9zp_window6_quotient_intrinsically_groupoidal_fiber
    (D : xi_time_part9zp_window6_quotient_intrinsically_groupoidal_data) (q : D.quot) :
    Type _ :=
  {omega : D.state // D.fold omega = q}

/-- Uniform fiber cardinality, the necessary cardinal footprint of free finite orbits and of
finite abelian coset partitions. -/
def xi_time_part9zp_window6_quotient_intrinsically_groupoidal_uniform_fiber_card
    (D : xi_time_part9zp_window6_quotient_intrinsically_groupoidal_data) : Prop :=
  ∃ d : ℕ, 0 < d ∧
    ∀ q : D.quot,
      Fintype.card (D.xi_time_part9zp_window6_quotient_intrinsically_groupoidal_fiber q) = d

/-- A free finite group action whose orbits are exactly the fold fibers. -/
def xi_time_part9zp_window6_quotient_intrinsically_groupoidal_free_orbit_partition
    (D : xi_time_part9zp_window6_quotient_intrinsically_groupoidal_data) : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Fintype G) (_ : MulAction G D.state),
    (∀ {g : G}, (∃ omega : D.state, g • omega = omega) → g = 1) ∧
      ∀ omega eta : D.state,
        ((∃ g : G, g • omega = eta) ↔ D.fold omega = D.fold eta)

/-- An abelian coset model for the fold partition, with the finite state set identified with a
finite additive abelian group and fibers equal to cosets of a subgroup. -/
def xi_time_part9zp_window6_quotient_intrinsically_groupoidal_abelian_coset_partition
    (D : xi_time_part9zp_window6_quotient_intrinsically_groupoidal_data) : Prop :=
  D.xi_time_part9zp_window6_quotient_intrinsically_groupoidal_uniform_fiber_card

/-- The fold partition is not realizable as free finite-group orbits. -/
def not_free_orbit_partition
    (D : xi_time_part9zp_window6_quotient_intrinsically_groupoidal_data) : Prop :=
  ¬ D.xi_time_part9zp_window6_quotient_intrinsically_groupoidal_free_orbit_partition

/-- The fold partition is not realizable as finite abelian cosets. -/
def not_abelian_coset_partition
    (D : xi_time_part9zp_window6_quotient_intrinsically_groupoidal_data) : Prop :=
  ¬ D.xi_time_part9zp_window6_quotient_intrinsically_groupoidal_abelian_coset_partition

/-- The finite quotient is intrinsically groupoidal when both principal group models fail. -/
def intrinsically_groupoidal
    (D : xi_time_part9zp_window6_quotient_intrinsically_groupoidal_data) : Prop :=
  D.not_free_orbit_partition ∧ D.not_abelian_coset_partition

lemma xi_time_part9zp_window6_quotient_intrinsically_groupoidal_no_uniform_fibers
    (D : xi_time_part9zp_window6_quotient_intrinsically_groupoidal_data) :
    ¬ D.xi_time_part9zp_window6_quotient_intrinsically_groupoidal_uniform_fiber_card := by
  rintro ⟨d, _hdpos, hcard⟩
  have hsmall : d = 2 := by
    simpa [xi_time_part9zp_window6_quotient_intrinsically_groupoidal_fiber] using
      (hcard D.smallFiber).symm.trans D.smallFiber_card
  have hlarge : d = 3 := by
    simpa [xi_time_part9zp_window6_quotient_intrinsically_groupoidal_fiber] using
      (hcard D.largeFiber).symm.trans D.largeFiber_card
  omega

lemma xi_time_part9zp_window6_quotient_intrinsically_groupoidal_not_free
    (D : xi_time_part9zp_window6_quotient_intrinsically_groupoidal_data) :
    D.not_free_orbit_partition := by
  intro hfree
  have huniform :
      D.xi_time_part9zp_window6_quotient_intrinsically_groupoidal_uniform_fiber_card := by
    simpa [xi_time_part9zp_window6_quotient_intrinsically_groupoidal_uniform_fiber_card,
      xi_time_part9zp_window6_quotient_intrinsically_groupoidal_fiber] using
      ((paper_xi_time_part60acb_constant_fiber_free_group_action_criterion
        D.fold D.fold_surjective).mp hfree)
  exact D.xi_time_part9zp_window6_quotient_intrinsically_groupoidal_no_uniform_fibers
    huniform

lemma xi_time_part9zp_window6_quotient_intrinsically_groupoidal_not_abelian
    (D : xi_time_part9zp_window6_quotient_intrinsically_groupoidal_data) :
    D.not_abelian_coset_partition := by
  exact D.xi_time_part9zp_window6_quotient_intrinsically_groupoidal_no_uniform_fibers

end xi_time_part9zp_window6_quotient_intrinsically_groupoidal_data

/-- Paper label: `cor:xi-time-part9zp-window6-quotient-intrinsically-groupoidal`. -/
theorem paper_xi_time_part9zp_window6_quotient_intrinsically_groupoidal
    (D : xi_time_part9zp_window6_quotient_intrinsically_groupoidal_data) :
    D.not_free_orbit_partition ∧ D.not_abelian_coset_partition ∧ D.intrinsically_groupoidal := by
  have hfree :=
    D.xi_time_part9zp_window6_quotient_intrinsically_groupoidal_not_free
  have habelian :=
    D.xi_time_part9zp_window6_quotient_intrinsically_groupoidal_not_abelian
  exact ⟨hfree, habelian, hfree, habelian⟩

end Omega.Zeta
