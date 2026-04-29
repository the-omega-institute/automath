import Omega.Zeta.XiZGHardcoreConstantResidue

namespace Omega.Zeta

noncomputable section

/-- Paper label: `cor:xi-zg-dirichlet-residue`. -/
theorem paper_xi_zg_dirichlet_residue :
    (let D := Omega.Zeta.xi_zg_hardcore_constant_residue_factorization_data
     let W := Omega.Zeta.xi_zg_hardcore_constant_residue_witness
     W.analytic.residueAtOne = D.hardcoreLimit / D.zetaEulerQuotient ∧
       0 < D.hardcoreLimit ∧ D.hardcoreLimit ≤ 1) := by
  dsimp
  have h := paper_xi_zg_hardcore_constant_residue
  dsimp [xi_zg_hardcore_constant_residue_statement] at h
  rcases h with ⟨hpos, hle, _hvalue, hresidue⟩
  exact ⟨hresidue, hpos, hle⟩

end

end Omega.Zeta
