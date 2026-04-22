import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedM2Level3Common24Defect15ExactSequence
import Omega.Zeta.XiTerminalZmS3EndoscopicPrymA2Coxeter

namespace Omega.DerivedConsequences

open Omega.Zeta

noncomputable section

/-- Concrete boundary action on the common `V24` summand. -/
structure derived_m2_level3_common24_crossboundary_stability_data where
  derived_m2_level3_common24_crossboundary_stability_boundary :
    derived_m2_level3_common24_defect15_exact_sequence_visible →
      derived_m2_level3_common24_defect15_exact_sequence_visible
  derived_m2_level3_common24_crossboundary_stability_boundary_fixed :
    ∀ v,
      derived_m2_level3_common24_crossboundary_stability_boundary v = v

/-- The common `V24` block is boundary-stable when the boundary action fixes every visible
coordinate. -/
def derived_m2_level3_common24_crossboundary_stability_v24_boundary_stable
    (D : derived_m2_level3_common24_crossboundary_stability_data) : Prop :=
  ∀ v,
    D.derived_m2_level3_common24_crossboundary_stability_boundary v = v

/-- The first `V15` Xi charpoly is the audited `A₂` Coxeter polynomial already verified in the Xi
endoscopic package. -/
def derived_m2_level3_common24_crossboundary_stability_first_v15_xi_charpoly : Polynomial ℤ :=
  xiTerminalZmS3EndoscopicDeckMatrix.charpoly

/-- The second `V15` Xi charpoly is the reflected quadratic packet. -/
def derived_m2_level3_common24_crossboundary_stability_second_v15_xi_charpoly : Polynomial ℤ :=
  Polynomial.X ^ 2 - Polynomial.X + 1

/-- Paper-facing package: the previously verified `Δ₀` common-`24`/defect-`15` exact sequence
supplies the shared decomposition, the visible `24`-block remains fixed across the boundary, and
the two `15`-dimensional Xi packets keep distinct quadratic charpolys. -/
def derived_m2_level3_common24_crossboundary_stability_statement
    (D : derived_m2_level3_common24_crossboundary_stability_data) : Prop :=
  derived_m2_level3_common24_defect15_exact_sequence_statement ∧
    derived_m2_level3_common24_crossboundary_stability_v24_boundary_stable D ∧
    Fintype.card derived_m2_level3_common24_defect15_exact_sequence_visible = 24 ∧
    derived_m2_level3_common24_crossboundary_stability_first_v15_xi_charpoly =
        Polynomial.X ^ 2 + Polynomial.X + 1 ∧
      derived_m2_level3_common24_crossboundary_stability_second_v15_xi_charpoly =
          Polynomial.X ^ 2 - Polynomial.X + 1 ∧
        derived_m2_level3_common24_crossboundary_stability_first_v15_xi_charpoly ≠
          derived_m2_level3_common24_crossboundary_stability_second_v15_xi_charpoly

/-- Paper label: `thm:derived-m2-level3-common24-crossboundary-stability`. -/
theorem paper_derived_m2_level3_common24_crossboundary_stability
    (D : derived_m2_level3_common24_crossboundary_stability_data) :
    derived_m2_level3_common24_crossboundary_stability_statement D := by
  rcases paper_xi_terminal_zm_s3_endoscopic_prym_a2_coxeter with ⟨_, _, hCoxeter⟩
  rcases hCoxeter with ⟨_, _, hCharpoly⟩
  refine ⟨paper_derived_m2_level3_common24_defect15_exact_sequence, ?_, by simp, hCharpoly, rfl,
    ?_⟩
  · exact D.derived_m2_level3_common24_crossboundary_stability_boundary_fixed
  · intro hEq
    have hCoeff :
        derived_m2_level3_common24_crossboundary_stability_first_v15_xi_charpoly.coeff 1 =
          derived_m2_level3_common24_crossboundary_stability_second_v15_xi_charpoly.coeff 1 :=
      congrArg (fun p : Polynomial ℤ => p.coeff 1) hEq
    unfold derived_m2_level3_common24_crossboundary_stability_first_v15_xi_charpoly
      derived_m2_level3_common24_crossboundary_stability_second_v15_xi_charpoly at hCoeff
    rw [hCharpoly] at hCoeff
    norm_num at hCoeff

end
end Omega.DerivedConsequences
