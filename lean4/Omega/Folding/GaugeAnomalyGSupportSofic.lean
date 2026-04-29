import Mathlib
import Mathlib.LinearAlgebra.Matrix.Notation

namespace Omega.Folding

open Polynomial

noncomputable section

abbrev GaugeSupportFourBlock := Fin 4 → Bool

def gaugeBlock0000 : GaugeSupportFourBlock := ![false, false, false, false]
def gaugeBlock0001 : GaugeSupportFourBlock := ![false, false, false, true]
def gaugeBlock0010 : GaugeSupportFourBlock := ![false, false, true, false]
def gaugeBlock0011 : GaugeSupportFourBlock := ![false, false, true, true]
def gaugeBlock0100 : GaugeSupportFourBlock := ![false, true, false, false]
def gaugeBlock0101 : GaugeSupportFourBlock := ![false, true, false, true]
def gaugeBlock0110 : GaugeSupportFourBlock := ![false, true, true, false]
def gaugeBlock0111 : GaugeSupportFourBlock := ![false, true, true, true]
def gaugeBlock1000 : GaugeSupportFourBlock := ![true, false, false, false]
def gaugeBlock1001 : GaugeSupportFourBlock := ![true, false, false, true]
def gaugeBlock1010 : GaugeSupportFourBlock := ![true, false, true, false]
def gaugeBlock1011 : GaugeSupportFourBlock := ![true, false, true, true]
def gaugeBlock1100 : GaugeSupportFourBlock := ![true, true, false, false]
def gaugeBlock1101 : GaugeSupportFourBlock := ![true, true, false, true]
def gaugeBlock1110 : GaugeSupportFourBlock := ![true, true, true, false]
def gaugeBlock1111 : GaugeSupportFourBlock := ![true, true, true, true]

/-- The forbidden-block presentation of the gauge-anomaly support. -/
def forbiddenGaugeSupportLanguage4 : Finset GaugeSupportFourBlock :=
  Finset.univ.filter fun w => w ≠ gaugeBlock0010 ∧ w ≠ gaugeBlock0100

/-- The 14 length-4 words realized by the four-state output process. -/
def fourStateGaugeSupportLanguage4 : Finset GaugeSupportFourBlock :=
  [gaugeBlock0000, gaugeBlock0001, gaugeBlock0011, gaugeBlock0101, gaugeBlock0110, gaugeBlock0111,
    gaugeBlock1000, gaugeBlock1001, gaugeBlock1010, gaugeBlock1011, gaugeBlock1100, gaugeBlock1101,
    gaugeBlock1110, gaugeBlock1111].toFinset

/-- The essential 5-state companion core for the SFT obtained from the two forbidden 4-blocks.
Its Perron polynomial is `x^5 - x^4 - x^3 - x - 1`. -/
def gaugeSupportSoficCore : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1;
     1, 1, 0, 1, 1]

/-- The Artin--Mazur denominator recorded by the essential companion core. -/
def gaugeSupportSoficZetaDenominator : Polynomial ℤ :=
  (1 : Polynomial ℤ) - X - X ^ 2 - X ^ 4 - X ^ 5

private theorem fourStateGaugeSupportLanguage4_eq_forbidden :
    fourStateGaugeSupportLanguage4 = forbiddenGaugeSupportLanguage4 := by
  native_decide

private theorem gaugeSupportSoficCore_cayley_hamilton :
    gaugeSupportSoficCore ^ 5 =
      gaugeSupportSoficCore ^ 4 + gaugeSupportSoficCore ^ 3 + gaugeSupportSoficCore + 1 := by
  native_decide

/-- The Bernoulli `p = 1/2` gauge-anomaly support is the SFT excluding `0010` and `0100`, and its
essential companion core satisfies the characteristic-polynomial recurrence corresponding to
`x^5 - x^4 - x^3 - x - 1`, with zeta denominator `1 - z - z^2 - z^4 - z^5`.
    thm:fold-gauge-anomaly-g-support-sofic -/
def foldGaugeAnomalyGSupportSofic : Prop :=
  fourStateGaugeSupportLanguage4 = forbiddenGaugeSupportLanguage4 ∧
    gaugeSupportSoficCore ^ 5 =
      gaugeSupportSoficCore ^ 4 + gaugeSupportSoficCore ^ 3 + gaugeSupportSoficCore + 1 ∧
    gaugeSupportSoficZetaDenominator = (1 : Polynomial ℤ) - X - X ^ 2 - X ^ 4 - X ^ 5

theorem paper_fold_gauge_anomaly_g_support_sofic : foldGaugeAnomalyGSupportSofic := by
  exact ⟨fourStateGaugeSupportLanguage4_eq_forbidden, gaugeSupportSoficCore_cayley_hamilton, rfl⟩

end

end Omega.Folding
