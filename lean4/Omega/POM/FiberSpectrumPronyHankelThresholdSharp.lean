import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic

namespace Omega.POM

open scoped fwdDiff

/-- The signed even/odd binomial moment gap attached to the sharpness counterexample family with
`n = 2r - 1`. Vanishing of this quantity means that the even and odd atomic spectra have the same
moments at order `k`. -/
def pomPronyHankelThresholdGap (r k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range ((2 * r - 1) + 1),
    ((-1 : ℤ) ^ (2 * r - 1 - j) * (Nat.choose (2 * r - 1) j : ℤ)) * ((j + 1 : ℤ) ^ k)

private lemma pomPronyHankelThresholdGap_eq_fwdDiff (r k : ℕ) :
    pomPronyHankelThresholdGap r k = (Δ_[(1 : ℤ)]^[2 * r - 1] (fun z : ℤ => z ^ k)) 1 := by
  simpa [pomPronyHankelThresholdGap, zsmul_eq_mul, one_nsmul, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc]
    using (fwdDiff_iter_eq_sum_shift (h := (1 : ℤ)) (f := fun z : ℤ => z ^ k) (2 * r - 1) 1).symm

/-- The explicit even/odd binomial split at `n = 2r - 1` has identical moments through order
`2r - 2`, but its top moment gap is the nonzero factorial value coming from the highest forward
difference. This packages the paper's sharp-threshold counterexample family in a concrete form.
    thm:pom-fiber-spectrum-prony-hankel-threshold-sharp -/
theorem paper_pom_fiber_spectrum_prony_hankel_threshold_sharp (r : ℕ) (hr : 2 ≤ r) :
    (∀ k : ℕ, k ≤ 2 * r - 2 → pomPronyHankelThresholdGap r k = 0) ∧
      pomPronyHankelThresholdGap r (2 * r - 1) = Nat.factorial (2 * r - 1) := by
  refine ⟨?_, ?_⟩
  · intro k hk
    rw [pomPronyHankelThresholdGap_eq_fwdDiff r k]
    have hklt : k < 2 * r - 1 := by omega
    simpa using congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ) hklt) 1
  · rw [pomPronyHankelThresholdGap_eq_fwdDiff r (2 * r - 1)]
    simpa using congrFun (fwdDiff_iter_eq_factorial (R := ℤ) (n := 2 * r - 1)) 1

end Omega.POM
