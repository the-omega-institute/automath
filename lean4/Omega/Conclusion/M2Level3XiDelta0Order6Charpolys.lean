import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Omega.Conclusion.M2Level3XiDelta0Order6Cycletypes

namespace Omega.Conclusion

open Polynomial

local notation "X" => (Polynomial.X : Polynomial ℤ)

noncomputable section

/-- Concrete wrapper for the audited order-`6` characteristic-polynomial statement. -/
structure ConclusionM2Level3XiDelta0Order6CharpolysData where
  conclusion_m2_level3_xi_delta0_order6_charpolys_witness : Unit := ()

/-- The order-`6` cyclotomic factor `Φ₁(X) = X - 1`. -/
def conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 : Polynomial ℤ :=
  X - 1

/-- The order-`6` cyclotomic factor `Φ₂(X) = X + 1`. -/
def conclusion_m2_level3_xi_delta0_order6_charpolys_phi2 : Polynomial ℤ :=
  X + 1

/-- The order-`6` cyclotomic factor `Φ₃(X) = X² + X + 1`. -/
def conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 : Polynomial ℤ :=
  X ^ 2 + X + 1

/-- The order-`6` cyclotomic factor `Φ₆(X) = X² - X + 1`. -/
def conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 : Polynomial ℤ :=
  X ^ 2 - X + 1

/-- Characteristic polynomial of the scalar line inside `QQ ⊕ V24 ⊕ V15`. -/
def conclusion_m2_level3_xi_delta0_order6_charpolys_scalar : Polynomial ℤ :=
  conclusion_m2_level3_xi_delta0_order6_charpolys_phi1

/-- Characteristic polynomial of the Steinberg local system `St`. -/
def conclusion_m2_level3_xi_delta0_order6_charpolys_St : Polynomial ℤ :=
  conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 ^ 15 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi2 ^ 12 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 ^ 15 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 ^ 12

/-- Characteristic polynomial of the common `V24` block. -/
def conclusion_m2_level3_xi_delta0_order6_charpolys_V24 : Polynomial ℤ :=
  conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 ^ 8 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi2 ^ 4 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 ^ 4 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 ^ 2

/-- Characteristic polynomial of the Klingen defect block `V15^Kl`. -/
def conclusion_m2_level3_xi_delta0_order6_charpolys_V15_Kl : Polynomial ℤ :=
  conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 ^ 5 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi2 ^ 4 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 ^ 2

/-- Characteristic polynomial of the Siegel defect block `V15^Si`. -/
def conclusion_m2_level3_xi_delta0_order6_charpolys_V15_Si : Polynomial ℤ :=
  conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 ^ 3 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 ^ 4 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 ^ 2

/-- The order-`6` Klingen-fiber characteristic polynomial coming from cycle type
`1^5 2^4 3^1 6^4`, written in cyclotomic-factor form. -/
def conclusion_m2_level3_xi_delta0_order6_charpolys_klingen_fiber : Polynomial ℤ :=
  conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 ^ 14 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi2 ^ 8 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 ^ 5 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 ^ 4

/-- The order-`6` Siegel-fiber characteristic polynomial coming from cycle type `1^4 3^4 6^4`,
written in cyclotomic-factor form. -/
def conclusion_m2_level3_xi_delta0_order6_charpolys_siegel_fiber : Polynomial ℤ :=
  conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 ^ 12 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi2 ^ 4 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 ^ 8 *
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 ^ 4

namespace ConclusionM2Level3XiDelta0Order6CharpolysData

/-- Concrete paper-facing formulation of the order-`6` characteristic-polynomial audit. -/
def Holds (_D : ConclusionM2Level3XiDelta0Order6CharpolysData) : Prop :=
  conclusion_m2_level3_xi_delta0_order6_cycletypes_klingen_cycle_counts = (5, 4, 1, 4) ∧
    conclusion_m2_level3_xi_delta0_order6_cycletypes_siegel_cycle_counts = (4, 0, 4, 4) ∧
    conclusion_m2_level3_xi_delta0_order6_charpolys_scalar =
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 ∧
    conclusion_m2_level3_xi_delta0_order6_charpolys_V24 =
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 ^ 8 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi2 ^ 4 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 ^ 4 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 ^ 2 ∧
    conclusion_m2_level3_xi_delta0_order6_charpolys_V15_Kl =
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 ^ 5 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi2 ^ 4 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 ^ 2 ∧
    conclusion_m2_level3_xi_delta0_order6_charpolys_V15_Si =
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 ^ 3 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 ^ 4 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 ^ 2 ∧
    conclusion_m2_level3_xi_delta0_order6_charpolys_St =
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 ^ 15 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi2 ^ 12 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 ^ 15 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 ^ 12 ∧
    conclusion_m2_level3_xi_delta0_order6_charpolys_scalar *
        conclusion_m2_level3_xi_delta0_order6_charpolys_V24 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_V15_Kl =
      conclusion_m2_level3_xi_delta0_order6_charpolys_klingen_fiber ∧
    conclusion_m2_level3_xi_delta0_order6_charpolys_scalar *
        conclusion_m2_level3_xi_delta0_order6_charpolys_V24 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_V15_Si =
      conclusion_m2_level3_xi_delta0_order6_charpolys_siegel_fiber

end ConclusionM2Level3XiDelta0Order6CharpolysData

private lemma conclusion_m2_level3_xi_delta0_order6_charpolys_X2_sub_one :
    (X ^ 2 - 1 : Polynomial ℤ) =
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi2 := by
  unfold conclusion_m2_level3_xi_delta0_order6_charpolys_phi1
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi2
  ring

private lemma conclusion_m2_level3_xi_delta0_order6_charpolys_X3_sub_one :
    (X ^ 3 - 1 : Polynomial ℤ) =
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 := by
  unfold conclusion_m2_level3_xi_delta0_order6_charpolys_phi1
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi3
  ring

private lemma conclusion_m2_level3_xi_delta0_order6_charpolys_X6_sub_one :
    (X ^ 6 - 1 : Polynomial ℤ) =
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi2 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 := by
  unfold conclusion_m2_level3_xi_delta0_order6_charpolys_phi1
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi2
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi3
    conclusion_m2_level3_xi_delta0_order6_charpolys_phi6
  ring

private lemma conclusion_m2_level3_xi_delta0_order6_charpolys_klingen_monomial_identity
    (a b c d : Polynomial ℤ) :
    a * (a ^ 8 * b ^ 4 * c ^ 4 * d ^ 2) * (a ^ 5 * b ^ 4 * c * d ^ 2) =
      a ^ 14 * b ^ 8 * c ^ 5 * d ^ 4 := by
  ring

private lemma conclusion_m2_level3_xi_delta0_order6_charpolys_siegel_monomial_identity
    (a b c d : Polynomial ℤ) :
    a * (a ^ 8 * b ^ 4 * c ^ 4 * d ^ 2) * (a ^ 3 * c ^ 4 * d ^ 2) =
      a ^ 12 * b ^ 4 * c ^ 8 * d ^ 4 := by
  ring

private lemma conclusion_m2_level3_xi_delta0_order6_charpolys_klingen_factorization :
    conclusion_m2_level3_xi_delta0_order6_charpolys_scalar *
        conclusion_m2_level3_xi_delta0_order6_charpolys_V24 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_V15_Kl =
      conclusion_m2_level3_xi_delta0_order6_charpolys_klingen_fiber := by
  simpa [conclusion_m2_level3_xi_delta0_order6_charpolys_scalar,
    conclusion_m2_level3_xi_delta0_order6_charpolys_V24,
    conclusion_m2_level3_xi_delta0_order6_charpolys_V15_Kl,
    conclusion_m2_level3_xi_delta0_order6_charpolys_klingen_fiber] using
    conclusion_m2_level3_xi_delta0_order6_charpolys_klingen_monomial_identity
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi1
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi2
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi3
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi6

private lemma conclusion_m2_level3_xi_delta0_order6_charpolys_siegel_factorization :
    conclusion_m2_level3_xi_delta0_order6_charpolys_scalar *
        conclusion_m2_level3_xi_delta0_order6_charpolys_V24 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_V15_Si =
      conclusion_m2_level3_xi_delta0_order6_charpolys_siegel_fiber := by
  simpa [conclusion_m2_level3_xi_delta0_order6_charpolys_scalar,
    conclusion_m2_level3_xi_delta0_order6_charpolys_V24,
    conclusion_m2_level3_xi_delta0_order6_charpolys_V15_Si,
    conclusion_m2_level3_xi_delta0_order6_charpolys_siegel_fiber] using
    conclusion_m2_level3_xi_delta0_order6_charpolys_siegel_monomial_identity
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi1
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi2
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi3
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi6

/-- Paper label: `thm:conclusion-m2-level3-xi-delta0-order6-charpolys`. The audited order-`6`
cycle types on the Klingen and Siegel fibers factor through the scalar line `St`, the common
`24`-dimensional block `V24`, and the two `15`-dimensional defect blocks, with the four block
characteristic polynomials recorded as explicit products of cyclotomic factors. -/
theorem paper_conclusion_m2_level3_xi_delta0_order6_charpolys
    (D : ConclusionM2Level3XiDelta0Order6CharpolysData) : D.Holds := by
  rcases paper_conclusion_m2_level3_xi_delta0_order6_cycletypes
      (D := ⟨()⟩) with ⟨_, _, _, hklingen, hsiegel, _⟩
  exact ⟨hklingen, hsiegel, rfl, rfl, rfl, rfl, rfl,
    conclusion_m2_level3_xi_delta0_order6_charpolys_klingen_factorization,
    conclusion_m2_level3_xi_delta0_order6_charpolys_siegel_factorization⟩

end
end Omega.Conclusion
