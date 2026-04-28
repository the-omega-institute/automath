import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62dca-hologram-bernoulli-lq-spectrum`. -/
theorem paper_xi_time_part62dca_hologram_bernoulli_lq_spectrum
    (B spectralBase tau : Real) (Z : Nat -> Real) (hB : 1 < B) (hZ0 : Z 0 = 1)
    (hZsucc : forall n : Nat, Z (n + 1) = spectralBase * Z n)
    (htau : tau = -Real.log spectralBase / Real.log B) :
    (forall n : Nat, Z n = spectralBase ^ n) /\
      tau = -Real.log spectralBase / Real.log B := by
  have _ : 1 < B := hB
  constructor
  · intro n
    induction n with
    | zero =>
        simpa using hZ0
    | succ n ih =>
        rw [hZsucc, ih]
        ring
  · exact htau

end Omega.Zeta
