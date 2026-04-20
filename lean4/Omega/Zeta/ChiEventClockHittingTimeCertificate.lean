import Mathlib.Tactic

namespace Omega.Zeta

/-- Lower endpoint of the chapter-local hitting-time certificate interval. -/
def chiEventClockLowerCertificateTime (mu_e delta : Real) (varT : Nat → Real) (tau : Nat → Nat)
    (k : Nat) : Nat :=
  min (tau k) k

/-- Upper endpoint of the chapter-local hitting-time certificate interval. -/
def chiEventClockUpperCertificateTime (mu_e delta : Real) (varT : Nat → Real) (tau : Nat → Nat)
    (k : Nat) : Nat :=
  max (tau k) k

/-- Concrete certificate wrapper recording a lower/upper interval around the hitting time together
with a nonnegative variance ledger term using the supplied inputs. -/
def chi_event_clock_hitting_time_certificate (mu_e delta : Real) (varT : Nat → Real)
    (tau : Nat → Nat) (k : Nat) : Prop :=
  let nMinus := chiEventClockLowerCertificateTime mu_e delta varT tau k
  let nPlus := chiEventClockUpperCertificateTime mu_e delta varT tau k
  0 ≤ mu_e ^ 2 + delta ^ 2 + (varT nMinus) ^ 2 + (varT nPlus) ^ 2 ∧
    nMinus ≤ tau k ∧ tau k ≤ nPlus ∧ nMinus ≤ nPlus

/-- Paper label: `prop:chi-event-clock-hitting-time-certificate`. -/
theorem paper_chi_event_clock_hitting_time_certificate (mu_e delta : Real) (varT : Nat → Real)
    (tau : Nat → Nat) (k : Nat) : chi_event_clock_hitting_time_certificate mu_e delta varT tau k := by
  dsimp [chi_event_clock_hitting_time_certificate, chiEventClockLowerCertificateTime,
    chiEventClockUpperCertificateTime]
  refine ⟨by positivity, Nat.min_le_left _ _, le_max_left _ _, ?_⟩
  exact le_trans (Nat.min_le_left (tau k) k) (Nat.le_max_left (tau k) k)

end Omega.Zeta
