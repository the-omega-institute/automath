import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Endpoint trace coordinate in the Laurent realization `u + u⁻¹`. -/
def endpointLiftS {p : ℕ} (u : Units (ZMod p)) : ZMod p :=
  (u : ZMod p) + (↑u⁻¹ : ZMod p)

/-- Endpoint anti-invariant coordinate in the Laurent realization `u - u⁻¹`. -/
def endpointLiftDelta {p : ℕ} (u : Units (ZMod p)) : ZMod p :=
  (u : ZMod p) - (↑u⁻¹ : ZMod p)

/-- Frobenius lift of the trace coordinate. -/
def endpointFrobeniusC (p : ℕ) (u : Units (ZMod p)) : ZMod p :=
  (u : ZMod p) ^ p + (↑u⁻¹ : ZMod p) ^ p

/-- Frobenius lift of the anti-invariant coordinate. -/
def endpointFrobeniusD (p : ℕ) (u : Units (ZMod p)) : ZMod p :=
  (u : ZMod p) ^ p - (↑u⁻¹ : ZMod p) ^ p

private lemma neg_one_pow_prime_zmod (p : ℕ) (hp : Nat.Prime p) :
    ((-1 : ZMod p) ^ p) = (-1 : ZMod p) := by
  by_cases htwo : p = 2
  · subst htwo
    decide
  · obtain ⟨k, hk⟩ := hp.odd_of_ne_two htwo
    rw [hk]
    simp [pow_add, pow_mul]

/-- In the Laurent realization `S = u + u⁻¹`, `δ = u - u⁻¹`, the Frobenius lift
`C = u^p + u⁻ᵖ`, `D = u^p - u⁻ᵖ` preserves the quadratic relation `D² = C² - 4`, and over
`ZMod p` the characteristic-`p` Frobenius identities recover `C = S^p` and `D = δ^p`.
    prop:endpoint-antiinv-frobenius-lift -/
theorem paper_endpoint_antiinv_frobenius_lift (p : ℕ) (hp : Nat.Prime p) (u : Units (ZMod p)) :
    let S := endpointLiftS u
    let δ := endpointLiftDelta u
    let C := endpointFrobeniusC p u
    let D := endpointFrobeniusD p u
    D ^ 2 = C ^ 2 - 4 ∧ C = S ^ p ∧ D = δ ^ p := by
  letI : Fact p.Prime := ⟨hp⟩
  dsimp [endpointLiftS, endpointLiftDelta, endpointFrobeniusC, endpointFrobeniusD]
  set a : ZMod p := (u : ZMod p)
  set b : ZMod p := (↑u⁻¹ : ZMod p)
  have hab : a * b = 1 := by
    change (↑u : ZMod p) * (↑u⁻¹ : ZMod p) = 1
    exact Units.mul_inv u
  have habPow : a ^ p * b ^ p = 1 := by
    calc
      a ^ p * b ^ p = (a * b) ^ p := by rw [mul_pow]
      _ = 1 := by simp [hab]
  have hC : (a ^ p + b ^ p : ZMod p) = (a + b) ^ p := by
    symm
    simpa using (add_pow_char (x := a) (y := b) p)
  have hnegb : (-b : ZMod p) ^ p = -b ^ p := by
    rw [neg_pow, neg_one_pow_prime_zmod p hp]
    simp
  have hD : (a ^ p - b ^ p : ZMod p) = (a - b) ^ p := by
    symm
    calc
      (a - b) ^ p = (a + -b) ^ p := by rw [sub_eq_add_neg]
      _ = a ^ p + (-b) ^ p := by simpa using (add_pow_char (x := a) (y := -b) p)
      _ = a ^ p - b ^ p := by rw [hnegb, sub_eq_add_neg]
  refine ⟨?_, ?_, ?_⟩
  · calc
      (a ^ p - b ^ p : ZMod p) ^ 2 = (a ^ p + b ^ p) ^ 2 - 4 * (a ^ p * b ^ p) := by ring
      _ = (a ^ p + b ^ p) ^ 2 - 4 := by rw [habPow]; ring
  · exact hC
  · exact hD

end Omega.UnitCirclePhaseArithmetic
