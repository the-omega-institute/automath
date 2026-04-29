import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.MicrocanonicalPosteriorModuliCLT
import Omega.POM.MicrocanonicalQueryDistortionStrongConversePlane

namespace Omega.POM

/-- Critical-window wrapper for the microcanonical query-distortion strong converse: once the
bit-density lies on the centered `√N` scale, the exact exponent from the strong-converse plane is
the logarithmic fluctuation coordinate from the posterior-moduli CLT package. -/
theorem paper_pom_microcanonical_query_distortion_critical_window_clt
    (beta bitDensity H_w V_w successExponent : ℝ) (hBeta0 : 0 ≤ beta) (hBeta1 : beta < 1)
    (hBits : 0 ≤ bitDensity)
    (hCritical :
      bitDensity * Real.log 2 =
        (1 - beta) * H_w + Real.sqrt (beta * (1 - beta)) * V_w)
    (hUpper : successExponent <= min 0 (bitDensity * Real.log 2 - (1 - beta) * H_w))
    (hLower : min 0 (bitDensity * Real.log 2 - (1 - beta) * H_w) <= successExponent) :
    successExponent =
      min 0
        (Real.log
          (Real.exp ((1 - beta) * H_w + Real.sqrt (beta * (1 - beta)) * V_w) /
            Real.exp ((1 - beta) * H_w))) := by
  have hPlane :=
    paper_pom_microcanonical_query_distortion_strong_converse_plane beta bitDensity H_w
      successExponent hBeta0 hBeta1 hBits hUpper hLower
  rcases paper_pom_microcanonical_posterior_moduli_clt beta H_w V_w with ⟨_, _, hLog⟩
  calc
    successExponent = min 0 (bitDensity * Real.log 2 - (1 - beta) * H_w) := hPlane
    _ = min 0 (Real.sqrt (beta * (1 - beta)) * V_w) := by rw [hCritical]; ring
    _ =
        min 0
          (Real.log
            (Real.exp ((1 - beta) * H_w + Real.sqrt (beta * (1 - beta)) * V_w) /
              Real.exp ((1 - beta) * H_w))) := by
                simpa using congrArg (fun x : ℝ => min 0 x) hLog.symm

end Omega.POM
