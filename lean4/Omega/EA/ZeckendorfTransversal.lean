import Omega.EA.FoldAsSectionCorollary
import Omega.EA.MonoidQuotientIsN
import Omega.EA.PrimeRegisterOrbitFiberCoincidence

namespace Omega.EA

open Omega.Rewrite

/-- Paper-facing statement: every valuation fiber meets the stable Zeckendorf section
    `R_F(ℕ)` in the unique irreducible representative `R_F (valPr a)`. -/
def paper_zeckendorf_transversal_stmt (a : Omega.Rewrite.DigitCfg) : Prop :=
  PrimeRegisterOrbit a (R_F (valPr a)) ∧
    Irreducible (R_F (valPr a)) ∧
    R_F (valPr a) ∈ PrimeRegister ∧
    ∀ b : Omega.Rewrite.DigitCfg, Irreducible b → valPr b = valPr a → b = R_F (valPr a)

theorem paper_zeckendorf_transversal (a : Omega.Rewrite.DigitCfg) :
    paper_zeckendorf_transversal_stmt a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (paper_prime_register_orbit_fiber_coincidence a (R_F (valPr a))).2 (by
      show valPr (R_F (valPr a)) = valPr a
      simp)
  · simpa [NF_pr] using (paper_prime_register_normal_form_uniqueness a).2.1
  · exact ⟨valPr a, rfl⟩
  · intro b hbIrr hbVal
    have hbEq : b = NF_pr b :=
      (paper_prime_register_normal_form_uniqueness b).2.2 b Relation.ReflTransGen.refl hbIrr
    calc
      b = NF_pr b := hbEq
      _ = R_F (valPr b) := rfl
      _ = R_F (valPr a) := by simp [hbVal]

end Omega.EA
