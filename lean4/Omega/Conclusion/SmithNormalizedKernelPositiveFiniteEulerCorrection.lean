import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The partial sums `s_p(k) = Σ_i min(k, e_i(p))` attached to a prime-specific Smith exponent
profile. -/
def smithPartialSum (profile : List ℕ) (k : ℕ) : ℕ :=
  (profile.map (Nat.min k)).sum

/-- The local prime-power coefficient `p^{s_p(k)}`. -/
def smithLocalTerm (p : ℕ) (profile : List ℕ) (k : ℕ) : ℕ :=
  p ^ smithPartialSum profile k

/-- The positive coefficient expected in the stabilized local numerator
`Q_{A,p}(X) / (1 - X)`. -/
def smithLocalCoeff (p : ℕ) (profile : List ℕ) (k : ℕ) : ℕ :=
  smithLocalTerm p profile k - smithLocalTerm p profile (k - 1)

/-- Evaluation of the finite bad-prime correction at a real parameter `X`. -/
def smithGlobalCorrection (S : Finset ℕ) (profile : ℕ → List ℕ) (cut : ℕ → ℕ) (X : ℝ) : ℝ :=
  Finset.prod S fun p =>
    1 + Finset.sum (Finset.Icc 1 (cut p)) fun k =>
      (smithLocalCoeff p (profile p) k : ℝ) * X ^ k

/-- The zeta-style simple pole factor. -/
def smithZetaKernel (X : ℝ) : ℝ :=
  1 / (1 - X)

/-- Concrete finite Euler-factor model for the normalized kernel Dirichlet series. -/
def smithGlobalDirichlet (S : Finset ℕ) (profile : ℕ → List ℕ) (cut : ℕ → ℕ) (X : ℝ) : ℝ :=
  smithZetaKernel X * smithGlobalCorrection S profile cut X

/-- The local prime-power terms stabilize once the index passes the cutoff. -/
def smithProfileStabilizes (profile : ℕ → List ℕ) (cut : ℕ → ℕ) : Prop :=
  ∀ p k, cut p ≤ k → smithPartialSum (profile p) k = smithPartialSum (profile p) (cut p)

/-- The global Dirichlet model is a zeta factor times a finite bad-prime correction, and the
underlying prime-power terms have stabilized at the chosen cutoffs. -/
def smithEulerFactorization (S : Finset ℕ) (profile : ℕ → List ℕ) (cut : ℕ → ℕ) : Prop :=
  smithProfileStabilizes profile cut ∧
    ∀ X : ℝ, smithGlobalDirichlet S profile cut X = smithZetaKernel X * smithGlobalCorrection S profile cut X

/-- Every local numerator coefficient in the bad-prime correction is strictly positive. -/
def smithLocalCorrectionPositive (S : Finset ℕ) (profile : ℕ → List ℕ) (cut : ℕ → ℕ) : Prop :=
  ∀ p ∈ S, ∀ k, 1 ≤ k → k ≤ cut p → 0 < smithLocalCoeff p (profile p) k

/-- The only possible pole of the zeta-kernel factor is at `X = 1`. -/
def smithUniquePoleAtOne : Prop :=
  ∀ X : ℝ, 1 - X = 0 ↔ X = 1

lemma smithPartialSum_stabilizes_list (profile : List ℕ) (cut k : ℕ)
    (hcut : ∀ i ∈ profile, i ≤ cut) (hk : cut ≤ k) :
    smithPartialSum profile k = smithPartialSum profile cut := by
  unfold smithPartialSum
  induction profile with
  | nil =>
      simp
  | cons a profile ih =>
      have ha : a ≤ cut := hcut a (by simp)
      have htail : ∀ i ∈ profile, i ≤ cut := by
        intro i hi
        exact hcut i (by simp [hi])
      have hmin : Nat.min k a = Nat.min cut a := by
        have hkmin : k.min a = a := Nat.min_eq_right (le_trans ha hk)
        have hcmin : cut.min a = a := Nat.min_eq_right ha
        simpa [Nat.min_comm] using hkmin.trans hcmin.symm
      simp [hmin, ih htail]

/-- The paper-facing normalized-kernel Euler factorization package: stabilization after the
Smith cutoff, positive bad-prime correction coefficients, and the unique pole carried by the
zeta factor.
    thm:conclusion-smith-normalized-kernel-positive-finite-euler-correction -/
theorem paper_conclusion_smith_normalized_kernel_positive_finite_euler_correction
    (S : Finset ℕ) (profile : ℕ → List ℕ) (cut : ℕ → ℕ)
    (hcut : ∀ p i, i ∈ profile p → i ≤ cut p)
    (hjump :
      ∀ p k, 1 ≤ k → k ≤ cut p → smithPartialSum (profile p) (k - 1) < smithPartialSum (profile p) k)
    (hprime : ∀ p ∈ S, 2 ≤ p) :
    smithEulerFactorization S profile cut ∧
      smithLocalCorrectionPositive S profile cut ∧
      smithUniquePoleAtOne := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro p k hk
      exact smithPartialSum_stabilizes_list (profile p) (cut p) k (hcut p) hk
    · intro X
      rfl
  · intro p hpS k hk1 hkcut
    unfold smithLocalCoeff smithLocalTerm
    have hp1 : 1 < p := lt_of_lt_of_le (by omega) (hprime p hpS)
    have hpow :
        p ^ smithPartialSum (profile p) (k - 1) < p ^ smithPartialSum (profile p) k := by
      exact Nat.pow_lt_pow_right hp1 (hjump p k hk1 hkcut)
    exact Nat.sub_pos_of_lt hpow
  · intro X
    constructor
    · intro hX
      linarith
    · intro hX
      linarith

end
end Omega.Conclusion
