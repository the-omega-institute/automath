import Mathlib.Tactic

namespace Omega.POM

/-- The partition monomial attached to the single-cycle partition `ν_r = (r, 1^(q-r))`. -/
def pom_schur_traces_determine_low_moments_partitionMonomial (S : ℕ → ℚ) (q r : ℕ) : ℚ :=
  S r * (S 1) ^ (q - r)

/-- The `r`-th Schur single-cycle trace readout. -/
def pom_schur_traces_determine_low_moments_singleCycleTrace (T : ℕ → ℚ) (r : ℕ) : ℚ :=
  T r

/-- Paper label: `cor:pom-schur-traces-determine-low-moments`. If the single-cycle Schur traces
recover the partition monomials `S_r(m) * S_1(m)^(q-r)` and the first moment is the known total
mass `2^m`, then dividing by that first moment recovers every low-order collision moment. -/
theorem paper_pom_schur_traces_determine_low_moments (q m : ℕ) (S T : ℕ → ℚ)
    (hS1 : S 1 = (2 : ℚ) ^ m)
    (hTrace :
      ∀ r : ℕ, 1 ≤ r → r ≤ q →
        pom_schur_traces_determine_low_moments_singleCycleTrace T r =
          pom_schur_traces_determine_low_moments_partitionMonomial S q r) :
    ∀ r : ℕ, 1 ≤ r → r ≤ q →
      S r =
        pom_schur_traces_determine_low_moments_singleCycleTrace T r /
          ((2 : ℚ) ^ m) ^ (q - r) := by
  intro r hr1 hrq
  have hTrace_r := hTrace r hr1 hrq
  rw [pom_schur_traces_determine_low_moments_singleCycleTrace,
    pom_schur_traces_determine_low_moments_partitionMonomial, hS1] at hTrace_r
  have hpow_ne : (((2 : ℚ) ^ m) ^ (q - r)) ≠ 0 := by
    exact pow_ne_zero _ (pow_ne_zero _ (by norm_num))
  apply (eq_div_iff hpow_ne).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hTrace_r.symm

end Omega.POM
