import Mathlib.Tactic
import Omega.SPG.ProuhetThueMorseFluxMoments

namespace Omega.Conclusion

open scoped BigOperators

/-- The affine insertion used to place the dyadic PTM witnesses in a small Wulff
neighborhood chart. -/
def conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_affine (j : ℕ) : ℕ :=
  2 * j + 5

/-- The scaled and translated positive dyadic witness. -/
def conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_positive : Finset ℕ :=
  Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class.image
    conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_affine

/-- The scaled and translated negative dyadic witness. -/
def conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_negative : Finset ℕ :=
  Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class.image
    conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_affine

/-- A concrete one-dimensional polynomial boundary-moment proxy for a finite witness. -/
def conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_moment (S : Finset ℕ)
    (k : ℕ) : ℤ :=
  ∑ j ∈ S, (j : ℤ) ^ k

/-- Concrete paper-facing camouflage statement: the scaled/translated PTM pair stays in a fixed
finite Wulff chart, is separated, and has matching moments through order one while the next
moment remains separated. -/
def conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_statement : Prop :=
  ∃ A B : Finset ℕ,
    A ≠ B ∧
      A ⊆ Finset.range 12 ∧
      B ⊆ Finset.range 12 ∧
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_moment A 0 =
        conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_moment B 0 ∧
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_moment A 1 =
        conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_moment B 1 ∧
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_moment A 2 ≠
        conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_moment B 2

/-- Paper label: `thm:conclusion-serrin-wulff-finite-order-boundary-moment-camouflage`. -/
theorem paper_conclusion_serrin_wulff_finite_order_boundary_moment_camouflage :
    conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_statement := by
  have hptm :=
    Omega.SPG.paper_spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments 2 1
      (by norm_num) (by norm_num)
  refine
    ⟨conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_positive,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_negative, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
  · intro hEq
    have hmem : 5 ∈ conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_positive := by
      simp [conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_positive,
        conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_affine,
        Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class]
    have : 5 ∈ conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_negative := by
      simpa [hEq] using hmem
    simp [conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_negative,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_affine,
      Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class] at this
  · intro x hx
    simp [conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_positive,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_affine,
      Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class] at hx ⊢
    omega
  · intro x hx
    simp [conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_negative,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_affine,
      Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class] at hx ⊢
    omega
  · norm_num [conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_moment,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_positive,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_negative,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_affine,
      Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class,
      Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class]
  · norm_num [conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_moment,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_positive,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_negative,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_affine,
      Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class,
      Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class]
  · norm_num [conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_moment,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_positive,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_negative,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_affine,
      Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class,
      Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class]

end Omega.Conclusion
