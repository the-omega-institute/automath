import Mathlib.Tactic
import Omega.GU.Window6PushEnvelopeCertificateUpgrade

namespace Omega.GU

/-- The commutator generators produced by the audited window-`6` envelope land in the skew part. -/
def window6CommutatorGeneratorsLandInSkewPart : Prop :=
  window6CommutatorSeedIsSkew

/-- Orthogonal-side certificate for the audited window-`6` Lie envelope. -/
def window6OrthogonalEnvelopeCertificate : Prop :=
  window6CommutatorGeneratorsLandInSkewPart ∧
    window6PushEnvelopeCertificate.commutatorTarget = .orthogonal ∧
    window6PushEnvelopeCertificate.ambientDimension = 21 ∧
    window6PushEnvelopeCertificate.orthogonalDimension =
      window6PushEnvelopeCertificate.ambientDimension *
        (window6PushEnvelopeCertificate.ambientDimension - 1) / 2 ∧
    window6PushEnvelopeCertificate.orthogonalDimension = 210

/-- Publication-facing wrapper for the audited window-`6` commutator envelope: the generators are
skew, the target is the orthogonal algebra on a `21`-dimensional space, and the audited lower
bound matches the sharp dimension formula `dim so(21) = 210`.
    thm:window6-lie-envelope-so21-from-commutators -/
theorem paper_window6_lie_envelope_so21_from_commutators :
    window6OrthogonalEnvelopeCertificate := by
  have hcert := paper_window6_push_envelope_certificate_upgrade
  rcases hcert with ⟨horth, _, hdim⟩
  rcases horth with ⟨hskew, htarget, hambient, hformula⟩
  rcases hdim with ⟨hdim210, _, _, _, _⟩
  exact ⟨hskew, htarget, hambient, hformula, hdim210⟩

end Omega.GU
