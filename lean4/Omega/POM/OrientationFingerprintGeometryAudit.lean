import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-orientation-fingerprint-geometry-audit`. The orientation fingerprint
is obtained by substituting the scan-sign edge parity and inversion-sign time-reversal formulas
into the defining pair. -/
theorem paper_pom_orientation_fingerprint_geometry_audit
    (X : Type) (chi : X -> Int × Int) (V E P : X -> Nat)
    (scanSign inversionSign : X -> Int)
    (hchi : forall x, chi x = (scanSign x, inversionSign x))
    (hscan : forall x, scanSign x = (-1 : Int) ^ E x)
    (hinv : forall x, inversionSign x = (-1 : Int) ^ ((V x - P x) / 2)) :
    forall x, chi x = ((-1 : Int) ^ E x, (-1 : Int) ^ ((V x - P x) / 2)) := by
  intro x
  rw [hchi x, hscan x, hinv x]

end Omega.POM
