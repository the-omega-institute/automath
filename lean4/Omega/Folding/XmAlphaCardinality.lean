import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Fib.Basic
import Omega.Folding.OstrowskiDenominators

namespace Omega.Folding

open Omega.Folding.OstrowskiDenominators

/-- Concrete finite admissible-digit family packaged by the Ostrowski denominator count at the
given length. -/
abbrev xm_alpha_cardinality_admissibleFamily (a : ℕ → ℕ) : ℕ → Type
  | n => Fin (ostrowskiDenom a (n + 1))

/-- The admissible-family cardinality is the corresponding Ostrowski denominator. -/
theorem xm_alpha_cardinality_admissibleFamily_card (a : ℕ → ℕ) (n : ℕ) :
    Fintype.card (xm_alpha_cardinality_admissibleFamily a n) = ostrowskiDenom a (n + 1) := by
  simp [xm_alpha_cardinality_admissibleFamily]

/-- Golden degeneration for the recursively packaged admissible family. -/
theorem xm_alpha_cardinality_admissibleFamily_golden_degeneration (n : ℕ) :
    Fintype.card (xm_alpha_cardinality_admissibleFamily (fun _ => 1) n) = Nat.fib (n + 2) := by
  simpa [xm_alpha_cardinality_admissibleFamily, Nat.add_assoc] using
    ostrowskiDenom_const_one_eq_fib (n + 1)

/-- Concrete package for the paper-level admissible-digit cardinality statement. -/
structure XmAlphaCardinalityData where
  partialQuotient : ℕ → ℕ
  length : ℕ

/-- The finite admissible family at the requested length. -/
def XmAlphaCardinalityData.admissibleFamily (D : XmAlphaCardinalityData) : Type :=
  xm_alpha_cardinality_admissibleFamily D.partialQuotient D.length

instance (D : XmAlphaCardinalityData) : Fintype D.admissibleFamily :=
  by
    dsimp [XmAlphaCardinalityData.admissibleFamily, xm_alpha_cardinality_admissibleFamily]
    infer_instance

/-- Cardinality of the finite admissible family. -/
def XmAlphaCardinalityData.admissibleCount (D : XmAlphaCardinalityData) : ℕ :=
  Fintype.card D.admissibleFamily

/-- Paper label: `prop:Xm-alpha-cardinality`. -/
theorem paper_xm_alpha_cardinality (D : XmAlphaCardinalityData) :
    D.admissibleCount =
      Omega.Folding.OstrowskiDenominators.ostrowskiDenom D.partialQuotient (D.length + 1) := by
  simpa [
    XmAlphaCardinalityData.admissibleCount,
    XmAlphaCardinalityData.admissibleFamily,
    xm_alpha_cardinality_admissibleFamily
  ] using
    xm_alpha_cardinality_admissibleFamily_card D.partialQuotient D.length

end Omega.Folding
