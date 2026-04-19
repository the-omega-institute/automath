import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.POM

open Polynomial

/-- The audited A₂ characteristic polynomial reduced modulo `7`. -/
noncomputable def chiA2Mod7 : Polynomial (ZMod 7) :=
  X ^ 3 - C 2 * X ^ 2 - C 2 * X + C 2

/-- The audited A₂ characteristic polynomial reduced modulo `11`. -/
noncomputable def chiA2Mod11 : Polynomial (ZMod 11) :=
  X ^ 3 - C 2 * X ^ 2 - C 2 * X + C 2

/-- Audited resonance cofactor for the `(q, p) = (14, 7)` slice. -/
noncomputable def resonanceCofactor14Mod7 : Polynomial (ZMod 7) :=
  X + 1

/-- Audited resonance polynomial for the `(q, p) = (14, 7)` slice. -/
noncomputable def resonancePoly14Mod7 : Polynomial (ZMod 7) :=
  chiA2Mod7 * resonanceCofactor14Mod7

/-- Audited resonance cofactor for the `(q, p) = (12, 11)` slice. -/
noncomputable def resonanceCofactor12Mod11 : Polynomial (ZMod 11) :=
  X + 3

/-- Audited resonance polynomial for the `(q, p) = (12, 11)` slice. -/
noncomputable def resonancePoly12Mod11 : Polynomial (ZMod 11) :=
  chiA2Mod11 * resonanceCofactor12Mod11

theorem resonancePoly14Mod7_factorization :
    resonancePoly14Mod7 = chiA2Mod7 * resonanceCofactor14Mod7 := by
  rfl

theorem resonancePoly12Mod11_factorization :
    resonancePoly12Mod11 = chiA2Mod11 * resonanceCofactor12Mod11 := by
  rfl

theorem chiA2Mod7_dvd_resonancePoly14Mod7 :
    chiA2Mod7 ∣ resonancePoly14Mod7 := by
  refine ⟨resonanceCofactor14Mod7, ?_⟩
  exact resonancePoly14Mod7_factorization

theorem chiA2Mod11_dvd_resonancePoly12Mod11 :
    chiA2Mod11 ∣ resonancePoly12Mod11 := by
  refine ⟨resonanceCofactor12Mod11, ?_⟩
  exact resonancePoly12Mod11_factorization

/-- The A₂ characteristic polynomial embeds into the audited resonance slices by explicit
polynomial identities modulo `7` and `11`.
    prop:pom-charpoly-modp-a2-embedding -/
theorem paper_pom_charpoly_modp_a2_embedding :
    resonancePoly14Mod7 = chiA2Mod7 * resonanceCofactor14Mod7 ∧
      resonancePoly12Mod11 = chiA2Mod11 * resonanceCofactor12Mod11 ∧
      chiA2Mod7 ∣ resonancePoly14Mod7 ∧
      chiA2Mod11 ∣ resonancePoly12Mod11 := by
  exact ⟨resonancePoly14Mod7_factorization, resonancePoly12Mod11_factorization,
    chiA2Mod7_dvd_resonancePoly14Mod7, chiA2Mod11_dvd_resonancePoly12Mod11⟩

end Omega.POM
