import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

namespace Omega.Zeta

/-- A finite reduced root-system shadow: the root set carries fixed-point-free central
symmetry.  This is the only root-system property needed for the odd-cardinality obstruction. -/
structure xi_time_part9zp_window6_odd_residual_root_closure_obstruction_reduced_finite_root_system where
  Root : Type
  rootFintype : Fintype Root
  neg : Root → Root
  neg_neg : Function.Involutive neg
  neg_ne : ∀ x, neg x ≠ x

/-- Cardinality of the finite root set in the prefixed root-system shadow. -/
def xi_time_part9zp_window6_odd_residual_root_closure_obstruction_root_card
    (R :
      xi_time_part9zp_window6_odd_residual_root_closure_obstruction_reduced_finite_root_system) :
    ℕ :=
  @Fintype.card R.Root R.rootFintype

/-- The concrete window-6 cardinal certificates used by the obstruction. -/
structure xi_time_part9zp_window6_odd_residual_root_closure_obstruction_certificate where
  X6 : Finset ℕ
  X6cyc : Finset ℕ
  X6_card : X6.card = 21
  X6cyc_card : X6cyc.card = 18

/-- Requested data name for the window-6 root-closure obstruction certificate. -/
abbrev xi_time_part9zp_window6_odd_residual_root_closure_obstruction_data :=
  xi_time_part9zp_window6_odd_residual_root_closure_obstruction_certificate

/-- Full `X₆` cannot have the cardinality of a finite reduced root system. -/
def xi_time_part9zp_window6_odd_residual_root_closure_obstruction_data.no_finite_reduced_root_system_for_X6
    (D : xi_time_part9zp_window6_odd_residual_root_closure_obstruction_data) : Prop :=
  ¬ ∃ R :
      xi_time_part9zp_window6_odd_residual_root_closure_obstruction_reduced_finite_root_system,
      xi_time_part9zp_window6_odd_residual_root_closure_obstruction_root_card R = D.X6.card

/-- A three-point completion of the cyclic 18 roots would again have odd cardinality. -/
def xi_time_part9zp_window6_odd_residual_root_closure_obstruction_data.no_three_point_completion
    (D : xi_time_part9zp_window6_odd_residual_root_closure_obstruction_data) : Prop :=
  ¬ ∃ R :
      xi_time_part9zp_window6_odd_residual_root_closure_obstruction_reduced_finite_root_system,
      xi_time_part9zp_window6_odd_residual_root_closure_obstruction_root_card R = D.X6cyc.card + 3

/-- A fixed-point-free central symmetry pairs all roots, so the root cardinality is even. -/
lemma xi_time_part9zp_window6_odd_residual_root_closure_obstruction_root_card_even
    (R :
      xi_time_part9zp_window6_odd_residual_root_closure_obstruction_reduced_finite_root_system) :
    Even (xi_time_part9zp_window6_odd_residual_root_closure_obstruction_root_card R) := by
  classical
  letI := R.rootFintype
  rw [xi_time_part9zp_window6_odd_residual_root_closure_obstruction_root_card]
  refine Nat.not_odd_iff_even.mp ?_
  intro hOdd
  have hcard : ¬ 2 ∣ Fintype.card R.Root := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hOdd) ((even_iff_two_dvd).2 hdiv)
  let σ : Equiv.Perm R.Root := Function.Involutive.toPerm R.neg R.neg_neg
  have hσpow : σ ^ (2 ^ 1) = 1 := by
    ext x
    simp [σ, pow_two, R.neg_neg x]
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hcard hσpow
  exact R.neg_ne x (by simpa [σ] using hx)

/-- Paper label: `thm:xi-time-part9zp-window6-odd-residual-root-closure-obstruction`. -/
theorem paper_xi_time_part9zp_window6_odd_residual_root_closure_obstruction
    (D : xi_time_part9zp_window6_odd_residual_root_closure_obstruction_data) :
    D.no_finite_reduced_root_system_for_X6 ∧ D.no_three_point_completion := by
  refine ⟨?_, ?_⟩
  · rintro ⟨R, hR⟩
    have heven :=
      xi_time_part9zp_window6_odd_residual_root_closure_obstruction_root_card_even R
    have hnotEven :
        ¬ Even (xi_time_part9zp_window6_odd_residual_root_closure_obstruction_root_card R) := by
      rw [hR, D.X6_card]
      norm_num
    exact hnotEven heven
  · rintro ⟨R, hR⟩
    have heven :=
      xi_time_part9zp_window6_odd_residual_root_closure_obstruction_root_card_even R
    have hnotEven :
        ¬ Even (xi_time_part9zp_window6_odd_residual_root_closure_obstruction_root_card R) := by
      rw [hR, D.X6cyc_card]
      norm_num
    exact hnotEven heven

end Omega.Zeta
