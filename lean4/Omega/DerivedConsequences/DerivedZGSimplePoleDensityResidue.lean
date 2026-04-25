import Omega.Zeta.XiZGHardcoreConstantResidue

namespace Omega.DerivedConsequences

open Omega.Zeta

/-- The concrete density/residue identification extracted from the standard ZG hard-core witness.
-/
def derived_zg_simple_pole_density_residue_statement : Prop :=
  let D := xi_zg_hardcore_constant_residue_factorization_data
  let W := xi_zg_hardcore_constant_residue_witness
  W.analytic.residueAtOne = W.analytic.deltaZG ∧
    W.analytic.deltaZG = D.hardcoreLimit / D.zetaEulerQuotient ∧
      D.hardcoreLimit = D.zetaEulerQuotient * W.analytic.deltaZG

/-- Paper label: `cor:derived-zg-simple-pole-density-residue`. -/
theorem paper_derived_zg_simple_pole_density_residue :
    derived_zg_simple_pole_density_residue_statement := by
  dsimp [derived_zg_simple_pole_density_residue_statement]
  let D := xi_zg_hardcore_constant_residue_factorization_data
  let W := xi_zg_hardcore_constant_residue_witness
  rcases paper_xi_zg_abel_residue_log_density W with ⟨habel, _, _⟩
  rcases paper_xi_zg_hardcore_constant_residue with ⟨_, _, _, hratio⟩
  have hresidue : W.analytic.residueAtOne = W.analytic.deltaZG := habel.1
  have hdensity :
      W.analytic.deltaZG = D.hardcoreLimit / D.zetaEulerQuotient := by
    calc
      W.analytic.deltaZG = W.analytic.residueAtOne := hresidue.symm
      _ = D.hardcoreLimit / D.zetaEulerQuotient := hratio
  have hzeta_ne : D.zetaEulerQuotient ≠ 0 := by
    norm_num [D, xi_zg_hardcore_constant_residue_factorization_data,
      Omega.Zeta.DerivedZGHardcoreFactorizationData.zetaEulerQuotient,
      Omega.Zeta.DerivedZGHardcoreFactorizationData.finiteZetaQuotient]
  have hhardcore :
      D.hardcoreLimit = W.analytic.deltaZG * D.zetaEulerQuotient := by
    exact (div_eq_iff hzeta_ne).mp hdensity.symm
  refine ⟨hresidue, hdensity, ?_⟩
  simpa [mul_comm] using hhardcore

end Omega.DerivedConsequences
