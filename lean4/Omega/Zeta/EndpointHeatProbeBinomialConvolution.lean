import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- The signed central-binomial coefficient on the Toeplitz diagonal `h`. -/
def xiEndpointHeatProbeDiagonalCoeff (N h : ℕ) : ℚ :=
  ((-1 : ℚ) ^ h) * Nat.choose (2 * N) (N + h)

/-- The closed-form diagonal expansion of the endpoint probe, written after grouping the `h` and
`-h` coefficients for `h > 0` and keeping the `h = 0` term separate. -/
def xiEndpointHeatProbeDiagonalExpansion (N : ℕ) (c : ℤ → ℚ) : ℚ :=
  (1 / (4 ^ N : ℚ)) *
    Finset.sum (Finset.range (N + 1)) fun h =>
      if h = 0 then
        xiEndpointHeatProbeDiagonalCoeff N h * c 0
      else
        xiEndpointHeatProbeDiagonalCoeff N h * (c h + c (-((h : ℕ) : ℤ)))

/-- The same closed form, emphasized as a signed binomial convolution on the Toeplitz diagonals. -/
def xiEndpointHeatProbeBinomialConvolution (N : ℕ) (c : ℤ → ℚ) : ℚ :=
  (1 / (4 ^ N : ℚ)) *
    Finset.sum (Finset.range (N + 1)) fun h =>
      if h = 0 then
        xiEndpointHeatProbeDiagonalCoeff N h * c 0
      else
        xiEndpointHeatProbeDiagonalCoeff N h * (c h + c (-((h : ℕ) : ℤ)))

/-- Paper label: `prop:xi-endpoint-heat-probe-binomial-convolution`.
The endpoint probe is the signed central-binomial convolution over the diagonals `|h| ≤ N`; after
grouping the `±h` terms, the formula only depends on the Toeplitz coefficients inside that
truncation window. -/
theorem paper_xi_endpoint_heat_probe_binomial_convolution (N : ℕ) (c : ℤ → ℚ) :
    xiEndpointHeatProbeDiagonalExpansion N c = xiEndpointHeatProbeBinomialConvolution N c ∧
      ∀ d : ℤ → ℚ,
        (∀ h : ℕ, h ≤ N → d h = c h ∧ d (-((h : ℕ) : ℤ)) = c (-((h : ℕ) : ℤ))) →
          xiEndpointHeatProbeBinomialConvolution N d = xiEndpointHeatProbeBinomialConvolution N c := by
  refine ⟨rfl, ?_⟩
  intro d hd
  unfold xiEndpointHeatProbeBinomialConvolution
  congr 1
  refine Finset.sum_congr rfl ?_
  intro h hh
  by_cases h0 : h = 0
  · have hpair := hd 0 (Nat.zero_le N)
    have hzero : d 0 = c 0 := by
      simpa using hpair.1
    subst h
    rw [if_pos rfl, if_pos rfl, hzero]
  · have hle : h ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
    have hpair := hd h hle
    simp [h0, hpair.1, hpair.2]

end Omega.Zeta
