import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete data for the endpoint binomial Toeplitz response. The `j`-th Toeplitz coefficient is
split into a constant dominant-pole part and a holomorphic error term bounded uniformly by the
Cauchy estimate `errorBound`. -/
structure XiBinomialToeplitzDominantPoleResponseData where
  N : ℕ
  dominantPole : ℝ
  holomorphicError : ℕ → ℝ
  errorBound : ℝ
  errorBound_nonneg : 0 ≤ errorBound
  cauchyBound : ∀ j : ℕ, j ≤ N → |holomorphicError j| ≤ errorBound

namespace XiBinomialToeplitzDominantPoleResponseData

/-- The endpoint quadratic Toeplitz weight on the `j`-th coefficient. -/
def endpointWeight (D : XiBinomialToeplitzDominantPoleResponseData) (j : ℕ) : ℝ :=
  (Nat.choose D.N j : ℝ) ^ 2

/-- The full coefficient split into dominant-pole and holomorphic-error parts. -/
def toeplitzCoeff (D : XiBinomialToeplitzDominantPoleResponseData) (j : ℕ) : ℝ :=
  D.dominantPole + D.holomorphicError j

/-- The endpoint quadratic response. -/
def endpointQuadraticResponse (D : XiBinomialToeplitzDominantPoleResponseData) : ℝ :=
  Finset.sum (Finset.range (D.N + 1)) fun j => D.endpointWeight j * D.toeplitzCoeff j

/-- The holomorphic remainder term after separating the pole part. -/
def holomorphicRemainder (D : XiBinomialToeplitzDominantPoleResponseData) : ℝ :=
  Finset.sum (Finset.range (D.N + 1)) fun j => D.endpointWeight j * D.holomorphicError j

/-- Closed-form evaluation of the dominant-pole contribution using the central-binomial identity. -/
def closedFormResponseLaw (D : XiBinomialToeplitzDominantPoleResponseData) : Prop :=
  D.endpointQuadraticResponse =
    (Nat.choose (2 * D.N) D.N : ℝ) * D.dominantPole + D.holomorphicRemainder

/-- The Cauchy error summed against the binomial mass is bounded by `errorBound * 4^N`. -/
def remainderBoundLaw (D : XiBinomialToeplitzDominantPoleResponseData) : Prop :=
  |D.holomorphicRemainder| ≤ D.errorBound * (4 : ℝ) ^ D.N

lemma endpointWeight_nonneg (D : XiBinomialToeplitzDominantPoleResponseData) (j : ℕ) :
    0 ≤ D.endpointWeight j := by
  unfold endpointWeight
  positivity

private lemma sum_endpointWeight_eq_centralBinom (D : XiBinomialToeplitzDominantPoleResponseData) :
    Finset.sum (Finset.range (D.N + 1)) (fun j => D.endpointWeight j) =
      (Nat.choose (2 * D.N) D.N : ℝ) := by
  unfold endpointWeight
  calc
    Finset.sum (Finset.range (D.N + 1)) (fun j => (Nat.choose D.N j : ℝ) ^ 2) =
        ((Finset.sum (Finset.range (D.N + 1)) (fun j => ((Nat.choose D.N j) ^ 2 : ℕ))) : ℝ) := by
          simp
    _ = (Nat.choose (2 * D.N) D.N : ℝ) := by
          exact_mod_cast (Nat.sum_range_choose_sq D.N)

private lemma centralBinom_le_four_pow (N : ℕ) : Nat.choose (2 * N) N ≤ 4 ^ N := by
  have hcentral :
      Nat.choose (2 * N) N ≤ Finset.sum (Finset.range (2 * N + 1)) (fun k => Nat.choose (2 * N) k) := by
    exact Finset.single_le_sum (f := fun k => Nat.choose (2 * N) k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))
  have hsum :
      Finset.sum (Finset.range (2 * N + 1)) (fun k => Nat.choose (2 * N) k) = 2 ^ (2 * N) := by
    simpa using Nat.sum_range_choose (2 * N)
  calc
    Nat.choose (2 * N) N ≤ 2 ^ (2 * N) := by simpa [hsum] using hcentral
    _ = 4 ^ N := by
      rw [pow_mul]
      norm_num

end XiBinomialToeplitzDominantPoleResponseData

open XiBinomialToeplitzDominantPoleResponseData

/-- Paper label: `thm:xi-binomial-toeplitz-dominant-pole-response`. Splitting the Toeplitz
coefficients into dominant-pole and holomorphic parts isolates the pole contribution via the
central-binomial identity, and the holomorphic remainder is bounded by the `4^N` binomial mass. -/
theorem paper_xi_binomial_toeplitz_dominant_pole_response
    (D : XiBinomialToeplitzDominantPoleResponseData) :
    D.closedFormResponseLaw ∧ D.remainderBoundLaw := by
  refine ⟨?_, ?_⟩
  · unfold XiBinomialToeplitzDominantPoleResponseData.closedFormResponseLaw
    unfold XiBinomialToeplitzDominantPoleResponseData.endpointQuadraticResponse
    unfold XiBinomialToeplitzDominantPoleResponseData.holomorphicRemainder
    unfold XiBinomialToeplitzDominantPoleResponseData.toeplitzCoeff
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    have hpole :
        Finset.sum (Finset.range (D.N + 1)) (fun j => D.endpointWeight j * D.dominantPole) =
          (Nat.choose (2 * D.N) D.N : ℝ) * D.dominantPole := by
      rw [← Finset.sum_mul]
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        congrArg (fun x : ℝ => x * D.dominantPole) (sum_endpointWeight_eq_centralBinom D)
    rw [hpole]
  · unfold XiBinomialToeplitzDominantPoleResponseData.remainderBoundLaw
    unfold XiBinomialToeplitzDominantPoleResponseData.holomorphicRemainder
    calc
      |Finset.sum (Finset.range (D.N + 1)) (fun j => D.endpointWeight j * D.holomorphicError j)| ≤
          Finset.sum (Finset.range (D.N + 1)) (fun j => |D.endpointWeight j * D.holomorphicError j|) := by
            simpa using
              (Finset.abs_sum_le_sum_abs (s := Finset.range (D.N + 1))
                (f := fun j => D.endpointWeight j * D.holomorphicError j))
      _ ≤ Finset.sum (Finset.range (D.N + 1)) (fun j => D.endpointWeight j * D.errorBound) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        have hjle : j ≤ D.N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hweight : 0 ≤ D.endpointWeight j := D.endpointWeight_nonneg j
        calc
          |D.endpointWeight j * D.holomorphicError j| =
              D.endpointWeight j * |D.holomorphicError j| := by
                rw [abs_mul, abs_of_nonneg hweight]
          _ ≤ D.endpointWeight j * D.errorBound := by
                gcongr
                exact D.cauchyBound j hjle
      _ = D.errorBound * Finset.sum (Finset.range (D.N + 1)) (fun j => D.endpointWeight j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
      _ ≤ D.errorBound * (4 : ℝ) ^ D.N := by
        have hcentral : (Nat.choose (2 * D.N) D.N : ℝ) ≤ (4 : ℝ) ^ D.N := by
          exact_mod_cast (centralBinom_le_four_pow D.N)
        rw [sum_endpointWeight_eq_centralBinom D]
        exact mul_le_mul_of_nonneg_left hcentral D.errorBound_nonneg

end Omega.Zeta
