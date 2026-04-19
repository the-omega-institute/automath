import Mathlib.Tactic
import Omega.GU.Window6LieTraceless
import Omega.GU.Window6PushEnvelopeCertificateUpgrade

namespace Omega.GU

/-- Publication-facing wrapper for the audited window-`6` full Lie-envelope certificate: the full
envelope target is `sl(21)`, its ambient space has dimension `21`, and the full-envelope
dimension is `21^2 - 1 = 440`.
    thm:window6-lie-envelope-sl21 -/
theorem paper_window6_lie_envelope_sl21 :
    window6PushEnvelopeCertificate.fullTarget = .specialLinear ∧
      window6PushEnvelopeCertificate.ambientDimension = 21 ∧
      window6PushEnvelopeCertificate.fullDimension =
        window6PushEnvelopeCertificate.ambientDimension ^ 2 - 1 ∧
      window6PushEnvelopeCertificate.fullDimension = 440 := by
  have hcert := paper_window6_push_envelope_certificate_upgrade
  rcases hcert with ⟨_, hfull, hdim⟩
  rcases hfull with ⟨_, htarget, hsl⟩
  rcases hdim with ⟨_, h440, _, _, _⟩
  exact ⟨htarget, rfl, hsl, h440⟩

end Omega.GU
