import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Omega.TypedAddressBiaxialCompletion.CayleyPreimageModulusCircle
import Omega.TypedAddressBiaxialCompletion.JensenEndpointAngleWindow

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete chapter-local data for the endpoint-compression reinterpretation of the time fiber.
The modulus parameter `rho` controls the two-ended Cayley preimage, while the endpoint window
data records the middle-window regime in which the high-height mass is concentrated near the
endpoint angle `-1`. -/
structure TimeFiberEndpointCompressionData where
  rho : ℝ
  hrho0 : 0 < rho
  hrho1 : rho < 1
  endpointWindow : JensenEndpointAngleWindowData
  endpointWindowMiddle :
    endpointWindow.yMinus < endpointWindow.cosThreshold ∧
      endpointWindow.cosThreshold < endpointWindow.yPlus

/-- The lower imaginary-axis intercept of the Cayley preimage circle is the boundary value
`(1 - ρ) / (1 + ρ)`, so the time fiber reaches arbitrarily low heights as `ρ ↑ 1`. -/
def TimeFiberEndpointCompressionData.touchesLowHeights
    (D : TimeFiberEndpointCompressionData) : Prop :=
  let c := (1 + D.rho ^ 2) / (1 - D.rho ^ 2)
  let r := (2 * D.rho) / (1 - D.rho ^ 2)
  c - r = (1 - D.rho) / (1 + D.rho)

/-- The upper imaginary-axis intercept of the Cayley preimage circle is the boundary value
`(1 + ρ) / (1 - ρ)`, so the same level set also reaches arbitrarily high heights as `ρ ↑ 1`. -/
def TimeFiberEndpointCompressionData.touchesHighHeights
    (D : TimeFiberEndpointCompressionData) : Prop :=
  let c := (1 + D.rho ^ 2) / (1 - D.rho ^ 2)
  let r := (2 * D.rho) / (1 - D.rho ^ 2)
  c + r = (1 + D.rho) / (1 - D.rho)

/-- In the middle window regime the admissible endpoint arc has the compressed complementary
formula `2 (π - arccos(cosThreshold))`. -/
def TimeFiberEndpointCompressionData.endpointWindowCompression
    (D : TimeFiberEndpointCompressionData) : Prop :=
  D.endpointWindow.angleWindowMeasure =
    2 * (Real.pi - Real.arccos D.endpointWindow.cosThreshold)

/-- Time-fiber endpoint compression package: the Cayley preimage circle touches both the low- and
high-height ends, and the high-height contribution is concentrated in the endpoint angle window.
    prop:typed-address-biaxial-completion-time-fiber-endpoint-compression -/
theorem paper_typed_address_biaxial_completion_time_fiber_endpoint_compression
    (D : TimeFiberEndpointCompressionData) :
    D.touchesLowHeights ∧ D.touchesHighHeights ∧ D.endpointWindowCompression := by
  rcases paper_app_cayley_preimage_modulus_circle D.rho D.hrho0 D.hrho1 with
    ⟨_, hLow, hHigh⟩
  rcases paper_app_jensen_endpoint_angle_window D.endpointWindow with
    ⟨_, hMiddle, _, _⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [TimeFiberEndpointCompressionData.touchesLowHeights] using hLow
  · simpa [TimeFiberEndpointCompressionData.touchesHighHeights] using hHigh
  · exact hMiddle D.endpointWindowMiddle.1 D.endpointWindowMiddle.2

end Omega.TypedAddressBiaxialCompletion
