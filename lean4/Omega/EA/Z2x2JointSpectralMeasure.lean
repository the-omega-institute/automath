import Mathlib.Tactic

namespace Omega.EA

open scoped BigOperators

/-- The four central-sign characters of the `Z₂ × Z₂` corner package. -/
abbrev Z2x2Character := Bool × Bool

/-- Convert a Boolean sign bit to the corresponding eigenvalue in `{±1}`. -/
def signOfBool : Bool → ℚ
  | true => 1
  | false => -1

/-- The scan-sign eigenvalue of a joint spectral point. -/
def scanEigenvalue (x : Z2x2Character) : ℚ :=
  signOfBool x.1

/-- The reversal-sign eigenvalue of a joint spectral point. -/
def revEigenvalue (x : Z2x2Character) : ℚ :=
  signOfBool x.2

/-- The normalized block trace attached to the block-size function `d`. -/
def normalizedBlockTrace (m : ℕ) (d : Z2x2Character → ℕ) : Z2x2Character → ℚ :=
  fun x => (d x : ℚ) / (2 ^ m : ℚ)

/-- Evaluate a bounded test function against the blockwise joint spectral data. -/
def jointSpectralAverage (m : ℕ) (d : Z2x2Character → ℕ) (f : ℚ × ℚ → ℚ) : ℚ :=
  ∑ x : Z2x2Character, normalizedBlockTrace m d x * f (scanEigenvalue x, revEigenvalue x)

/-- The explicit pushforward average on the four-point spectrum `{±1}²`. -/
def pushforwardAverage (m : ℕ) (d : Z2x2Character → ℕ) (f : ℚ × ℚ → ℚ) : ℚ :=
  normalizedBlockTrace m d (true, true) * f (1, 1) +
    normalizedBlockTrace m d (true, false) * f (1, -1) +
      normalizedBlockTrace m d (false, true) * f (-1, 1) +
        normalizedBlockTrace m d (false, false) * f (-1, -1)

/-- The signed `q`-moment traced against the blockwise `Z₂ × Z₂` spectrum. -/
def signedMomentTrace (m : ℕ) (d : Z2x2Character → ℕ) (s t q : ℕ) : ℚ :=
  ∑ x : Z2x2Character,
    normalizedBlockTrace m d x *
      scanEigenvalue x ^ s * revEigenvalue x ^ t * (d x : ℚ) ^ q

/-- The `Z₂ × Z₂` joint spectral measure is the pushforward of the normalized block trace, and
the signed moment is the corresponding blockwise weighted power sum.
    thm:fold-groupoid-z2x2-joint-spectral-measure -/
theorem paper_fold_groupoid_z2x2_joint_spectral_measure
    (m : ℕ) (d : Z2x2Character → ℕ) (hmass : ∑ x : Z2x2Character, d x = 2 ^ m) :
    (Finset.univ.sum (normalizedBlockTrace m d) = 1 ∧
      ∀ f : ℚ × ℚ → ℚ, jointSpectralAverage m d f = pushforwardAverage m d f) ∧
    ∀ q s t : ℕ,
      signedMomentTrace m d s t q =
        (1 / (2 ^ m : ℚ)) *
          ∑ x : Z2x2Character,
            scanEigenvalue x ^ s * revEigenvalue x ^ t * (d x : ℚ) ^ (q + 1) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have hpow_ne : (2 ^ m : ℚ) ≠ 0 := by positivity
      have hsum_cast : (∑ x : Z2x2Character, (d x : ℚ)) = 2 ^ m := by
        exact_mod_cast hmass
      calc
        Finset.univ.sum (normalizedBlockTrace m d)
            = (∑ x : Z2x2Character, (d x : ℚ)) / (2 ^ m : ℚ) := by
                simp [normalizedBlockTrace, Finset.sum_div]
        _ = (2 ^ m : ℚ) / (2 ^ m : ℚ) := by rw [hsum_cast]
        _ = 1 := by simp [hpow_ne]
    · intro f
      rw [jointSpectralAverage, Fintype.sum_prod_type]
      simp [pushforwardAverage, normalizedBlockTrace,
        scanEigenvalue, revEigenvalue, signOfBool]
      ring
  · intro q s t
    calc
      signedMomentTrace m d s t q
          = ∑ x : Z2x2Character,
              (1 / (2 ^ m : ℚ)) *
                (scanEigenvalue x ^ s * revEigenvalue x ^ t * (d x : ℚ) ^ (q + 1)) := by
              unfold signedMomentTrace normalizedBlockTrace
              refine Finset.sum_congr rfl ?_
              intro x hx
              rw [div_eq_mul_inv, pow_succ]
              ring
      _ = (1 / (2 ^ m : ℚ)) *
            ∑ x : Z2x2Character,
              scanEigenvalue x ^ s * revEigenvalue x ^ t * (d x : ℚ) ^ (q + 1) := by
              rw [← Finset.mul_sum]

end Omega.EA
