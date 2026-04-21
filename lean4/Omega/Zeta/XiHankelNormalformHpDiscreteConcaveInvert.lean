import Omega.Zeta.SmithPadicLossSpectrumClassification
import Omega.Zeta.XiHankelNormalformCRTAdelicMultiplicity

namespace Omega.Zeta

/-- The `H_p` profile attached to a Smith valuation multiset. -/
def xiHankelHp (s : Multiset ℕ) : ℕ → ℕ :=
  smithEntropy s

/-- First differences of the `H_p` profile. -/
def xiHankelHpFirstDiff (s : Multiset ℕ) (k : ℕ) : ℕ :=
  xiHankelHp s (k + 1) - xiHankelHp s k

/-- Kernel-size avatar of the `H_p` profile. -/
def xiHankelKernelSize (p : ℕ) (s : Multiset ℕ) (k : ℕ) : ℕ :=
  p ^ xiHankelHp s k

private lemma xiHankelHpFirstDiff_eq_delta (s : Multiset ℕ) (k : ℕ) :
    xiHankelHpFirstDiff s k = smithDelta s (k + 1) := by
  unfold xiHankelHpFirstDiff xiHankelHp
  rw [smithEntropy_succ_eq_add_delta]
  omega

private lemma xiHankelHp_eventually_constant (s : Multiset ℕ) {k : ℕ} (hk : s.sum ≤ k) :
    xiHankelHp s (k + 1) = xiHankelHp s k := by
  have hk0 : ∀ v ∈ s, v ≤ k := by
    intro v hv
    exact le_trans (le_sum_of_mem hv) hk
  have hk1 : ∀ v ∈ s, v ≤ k + 1 := by
    intro v hv
    exact le_trans (hk0 v hv) (Nat.le_succ _)
  unfold xiHankelHp
  rw [smithEntropy_eq_sum_of_all_le s (k + 1) hk1, smithEntropy_eq_sum_of_all_le s k hk0]

/-- The `H_p` profile is monotone and discretely concave, its first differences reconstruct the
valuation multiset, and exponentiating `H_p` gives the kernel-size profile.
    prop:xi-hankel-normalform-hp-discrete-concave-invert -/
theorem paper_xi_hankel_normalform_hp_discrete_concave_invert (s : Multiset ℕ) :
    xiHankelHp s 0 = 0 ∧
      (∀ k : ℕ, xiHankelHp s k ≤ xiHankelHp s (k + 1)) ∧
      (∀ k : ℕ, xiHankelHpFirstDiff s (k + 1) ≤ xiHankelHpFirstDiff s k) ∧
      (∀ k : ℕ, (s.filter fun v => v = k + 1).card =
        xiHankelHpFirstDiff s k - xiHankelHpFirstDiff s (k + 1)) ∧
      (∃ N : ℕ, ∀ k : ℕ, N ≤ k → xiHankelHp s (k + 1) = xiHankelHp s k) ∧
      (∀ p k : ℕ, xiHankelKernelSize p s k = p ^ xiHankelHp s k) := by
  refine ⟨smithEntropy_zero s, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact smithEntropy_mono_succ s k
  · intro k
    rw [xiHankelHpFirstDiff_eq_delta, xiHankelHpFirstDiff_eq_delta]
    exact smithDelta_antitone s (Nat.le_succ (k + 1))
  · intro k
    rw [xiHankelHpFirstDiff_eq_delta, xiHankelHpFirstDiff_eq_delta]
    exact smithMultiplicity_eq_delta_sub s (k + 1)
  · refine ⟨s.sum, ?_⟩
    intro k hk
    exact xiHankelHp_eventually_constant s hk
  · intro p k
    rfl

end Omega.Zeta
