import Mathlib.Tactic

namespace Omega.POM

/-- The abstract `q`-fold moment word accumulates anomaly additively under the supplied
recursion, hence its anomaly is the `q`-fold natural multiple of the input anomaly.
    prop:pom-anom-moment-amplification -/
theorem paper_pom_anom_moment_amplification {Word H : Type*} [AddCommMonoid H]
    (anom : Word → H) (compose : Word → Word → Word) (unit : Word)
    (mom : ℕ → Word → Word) (hzero : ∀ w, mom 0 w = unit)
    (hsucc : ∀ n w, mom (n + 1) w = compose w (mom n w))
    (hunit : anom unit = 0) (hadd : ∀ u v, anom (compose u v) = anom u + anom v)
    (q : ℕ) (w : Word) :
    anom (mom q w) = q • anom w := by
  induction q with
  | zero =>
      simp [hzero, hunit]
  | succ n ih =>
      calc
        anom (mom (n + 1) w) = anom (compose w (mom n w)) := by
          rw [hsucc]
        _ = anom w + anom (mom n w) := hadd w (mom n w)
        _ = anom w + n • anom w := by rw [ih]
        _ = (n + 1) • anom w := by rw [succ_nsmul']

end Omega.POM
