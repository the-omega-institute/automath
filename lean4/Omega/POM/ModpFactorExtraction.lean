import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.POM

open Polynomial

/-- Paper-label-prefixed ambient sequence space over `ZMod p`. -/
abbrev pom_modp_factor_extraction_sequence (p : ℕ) := ℕ → ZMod p

/-- Concrete data for extracting a lower-order mod-`p` recurrence from a factorization
`P = chi * Q`. The action field represents the chapter-local polynomial shift action `P(E)` on
sequences, and `action_mul` packages its multiplicativity. -/
structure pom_modp_factor_extraction_data where
  p : ℕ
  P : Polynomial (ZMod p)
  chi : Polynomial (ZMod p)
  Q : Polynomial (ZMod p)
  chi_monic : chi.Monic
  sequence : pom_modp_factor_extraction_sequence p
  action : Polynomial (ZMod p) →
    pom_modp_factor_extraction_sequence p → pom_modp_factor_extraction_sequence p
  action_mul :
    ∀ A B S, action (A * B) S = action A (action B S)
  factorization : P = chi * Q
  annihilated : action P sequence = 0

namespace pom_modp_factor_extraction_data

/-- The derived sequence obtained by applying `Q(E)` to the original sequence. -/
def derived_sequence (D : pom_modp_factor_extraction_data) :
    pom_modp_factor_extraction_sequence D.p :=
  D.action D.Q D.sequence

/-- The extracted subrecurrence: after factoring `P = chi * Q`, the derived sequence is killed
by `chi(E)`. -/
def extracted_subrecurrence (D : pom_modp_factor_extraction_data) : Prop :=
  D.action D.chi D.derived_sequence = 0

end pom_modp_factor_extraction_data

/-- Paper label: `prop:pom-modp-factor-extraction`. -/
theorem paper_pom_modp_factor_extraction (D : pom_modp_factor_extraction_data) :
    D.extracted_subrecurrence := by
  dsimp [pom_modp_factor_extraction_data.extracted_subrecurrence,
    pom_modp_factor_extraction_data.derived_sequence]
  rw [← D.action_mul]
  simpa [D.factorization] using D.annihilated

end Omega.POM
