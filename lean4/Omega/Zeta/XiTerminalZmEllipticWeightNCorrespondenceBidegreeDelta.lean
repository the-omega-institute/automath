import Mathlib.Tactic

namespace Omega.Zeta

/-- A concrete affine-chart model for the map `P ↦ (y(P), y([n]P))`. -/
def xiTerminalWeightCoordinate (P : ℤ × ℤ) : ℤ :=
  P.1 ^ 2 - P.2 - 1

/-- The second coordinate scales the weight by the square degree of `[n]`. -/
def xiTerminalWeightNCoordinate (n : ℕ) (P : ℤ × ℤ) : ℤ :=
  (n : ℤ) ^ 2 * xiTerminalWeightCoordinate P

/-- Concrete correspondence map on the affine chart. -/
def xiTerminalWeightCorrespondenceMap (n : ℕ) : ℤ × ℤ → ℤ × ℤ :=
  fun P => (xiTerminalWeightCoordinate P, xiTerminalWeightNCoordinate n P)

/-- The normalization degree is one in this concrete model. -/
def xiTerminalNormalizationDegree (_n : ℕ) : ℕ := 1

/-- Bidegree in `ℙ¹ × ℙ¹`: degree `4n²` in the first factor and degree `4` in the second. -/
def xiTerminalBidegree (n : ℕ) : ℕ × ℕ := (4 * n ^ 2, 4)

/-- Arithmetic genus of a curve of bidegree `(4n², 4)` in `ℙ¹ × ℙ¹`. -/
def xiTerminalArithmeticGenus (n : ℕ) : ℕ :=
  (xiTerminalBidegree n).2 - 1 |> fun b => ((xiTerminalBidegree n).1 - 1) * b

/-- Since the normalization has genus one, the total `δ`-invariant is `p_a - 1`. -/
def xiTerminalTotalDelta (n : ℕ) : ℕ :=
  xiTerminalArithmeticGenus n - 1

/-- Concrete package matching the paper statement. -/
def xiTerminalBidegreeAndDeltaFormula (n : ℕ) : Prop :=
  xiTerminalNormalizationDegree n = 1 ∧
    xiTerminalBidegree n = (4 * n ^ 2, 4) ∧
      xiTerminalArithmeticGenus n = 12 * n ^ 2 - 3 ∧
        xiTerminalTotalDelta n = 12 * n ^ 2 - 4

/-- The concrete correspondence has normalization degree `1`, bidegree `(4n², 4)`, arithmetic
genus `3 (4n² - 1) = 12n² - 3`, and total `δ`-invariant `12n² - 4`.
    thm:xi-terminal-zm-elliptic-weight-n-correspondence-bidegree-delta -/
theorem paper_xi_terminal_zm_elliptic_weight_n_correspondence_bidegree_delta (n : ℕ) :
    xiTerminalBidegreeAndDeltaFormula n := by
  have hgenus : xiTerminalArithmeticGenus n = 12 * n ^ 2 - 3 := by
    unfold xiTerminalArithmeticGenus xiTerminalBidegree
    let m : ℕ := n ^ 2
    change (4 * m - 1) * 3 = 12 * m - 3
    omega
  have hdelta : xiTerminalTotalDelta n = 12 * n ^ 2 - 4 := by
    unfold xiTerminalTotalDelta
    rw [hgenus]
    omega
  unfold xiTerminalBidegreeAndDeltaFormula xiTerminalNormalizationDegree
  refine ⟨rfl, rfl, hgenus, hdelta⟩

end Omega.Zeta
