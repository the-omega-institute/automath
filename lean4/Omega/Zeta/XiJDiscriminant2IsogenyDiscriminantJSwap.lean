import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The `b₂` invariant for a Weierstrass model with `a₁ = a₃ = 0`. -/
def xi_j_discriminant_2isogeny_discriminant_j_swap_b2 (a2 : ℚ) : ℚ :=
  4 * a2

/-- The `b₄` invariant for a Weierstrass model with `a₁ = a₃ = 0`. -/
def xi_j_discriminant_2isogeny_discriminant_j_swap_b4 (a4 : ℚ) : ℚ :=
  2 * a4

/-- The `b₆` invariant for a Weierstrass model with `a₁ = a₃ = 0`. -/
def xi_j_discriminant_2isogeny_discriminant_j_swap_b6 (a6 : ℚ) : ℚ :=
  4 * a6

/-- The `b₈` invariant for a Weierstrass model with `a₁ = a₃ = 0`. -/
def xi_j_discriminant_2isogeny_discriminant_j_swap_b8 (a2 a4 a6 : ℚ) : ℚ :=
  4 * a2 * a6 - a4 ^ 2

/-- The Weierstrass discriminant in the `a₁ = a₃ = 0` normalization. -/
def xi_j_discriminant_2isogeny_discriminant_j_swap_discriminant
    (a2 a4 a6 : ℚ) : ℚ :=
  -xi_j_discriminant_2isogeny_discriminant_j_swap_b2 a2 ^ 2 *
      xi_j_discriminant_2isogeny_discriminant_j_swap_b8 a2 a4 a6 -
    8 * xi_j_discriminant_2isogeny_discriminant_j_swap_b4 a4 ^ 3 -
    27 * xi_j_discriminant_2isogeny_discriminant_j_swap_b6 a6 ^ 2 +
    9 * xi_j_discriminant_2isogeny_discriminant_j_swap_b2 a2 *
      xi_j_discriminant_2isogeny_discriminant_j_swap_b4 a4 *
      xi_j_discriminant_2isogeny_discriminant_j_swap_b6 a6

/-- The `c₄` invariant in the `a₁ = a₃ = 0` normalization. -/
def xi_j_discriminant_2isogeny_discriminant_j_swap_c4 (a2 a4 : ℚ) : ℚ :=
  xi_j_discriminant_2isogeny_discriminant_j_swap_b2 a2 ^ 2 -
    24 * xi_j_discriminant_2isogeny_discriminant_j_swap_b4 a4

/-- The `j`-invariant obtained from `c₄³ / Δ`. -/
def xi_j_discriminant_2isogeny_discriminant_j_swap_jInvariant (a2 a4 a6 : ℚ) : ℚ :=
  xi_j_discriminant_2isogeny_discriminant_j_swap_c4 a2 a4 ^ 3 /
    xi_j_discriminant_2isogeny_discriminant_j_swap_discriminant a2 a4 a6

/-- The source curve `E_{A,B}` discriminant. -/
def xi_j_discriminant_2isogeny_discriminant_j_swap_sourceDiscriminant
    (A B : ℚ) : ℚ :=
  xi_j_discriminant_2isogeny_discriminant_j_swap_discriminant A B 0

/-- The two-isogenous curve `E'_{A,B}` discriminant. -/
def xi_j_discriminant_2isogeny_discriminant_j_swap_targetDiscriminant
    (A B : ℚ) : ℚ :=
  xi_j_discriminant_2isogeny_discriminant_j_swap_discriminant (-2 * A) (A ^ 2 - 4 * B) 0

/-- The source curve `j`-invariant. -/
def xi_j_discriminant_2isogeny_discriminant_j_swap_sourceJInvariant (A B : ℚ) : ℚ :=
  xi_j_discriminant_2isogeny_discriminant_j_swap_jInvariant A B 0

/-- The two-isogenous curve `j`-invariant. -/
def xi_j_discriminant_2isogeny_discriminant_j_swap_targetJInvariant (A B : ℚ) : ℚ :=
  xi_j_discriminant_2isogeny_discriminant_j_swap_jInvariant (-2 * A) (A ^ 2 - 4 * B) 0

/-- Odd-prime discriminant exponent pattern for `E_{A,B}`, ignoring the power of two. -/
def xi_j_discriminant_2isogeny_discriminant_j_swap_sourceOddExponent
    (_p eB eD : ℕ) : ℕ :=
  2 * eB + eD

/-- Odd-prime discriminant exponent pattern for `E'_{A,B}`, ignoring the power of two. -/
def xi_j_discriminant_2isogeny_discriminant_j_swap_targetOddExponent
    (_p eB eD : ℕ) : ℕ :=
  eB + 2 * eD

private lemma xi_j_discriminant_2isogeny_discriminant_j_swap_source_discriminant_closed
    (A B : ℚ) :
    xi_j_discriminant_2isogeny_discriminant_j_swap_sourceDiscriminant A B =
      2 ^ 4 * B ^ 2 * (A ^ 2 - 4 * B) := by
  unfold xi_j_discriminant_2isogeny_discriminant_j_swap_sourceDiscriminant
    xi_j_discriminant_2isogeny_discriminant_j_swap_discriminant
    xi_j_discriminant_2isogeny_discriminant_j_swap_b2
    xi_j_discriminant_2isogeny_discriminant_j_swap_b4
    xi_j_discriminant_2isogeny_discriminant_j_swap_b6
    xi_j_discriminant_2isogeny_discriminant_j_swap_b8
  ring

private lemma xi_j_discriminant_2isogeny_discriminant_j_swap_target_discriminant_closed
    (A B : ℚ) :
    xi_j_discriminant_2isogeny_discriminant_j_swap_targetDiscriminant A B =
      2 ^ 8 * B * (A ^ 2 - 4 * B) ^ 2 := by
  unfold xi_j_discriminant_2isogeny_discriminant_j_swap_targetDiscriminant
    xi_j_discriminant_2isogeny_discriminant_j_swap_discriminant
    xi_j_discriminant_2isogeny_discriminant_j_swap_b2
    xi_j_discriminant_2isogeny_discriminant_j_swap_b4
    xi_j_discriminant_2isogeny_discriminant_j_swap_b6
    xi_j_discriminant_2isogeny_discriminant_j_swap_b8
  ring

/-- Paper label: `thm:xi-j-discriminant-2isogeny-discriminant-j-swap`. -/
theorem paper_xi_j_discriminant_2isogeny_discriminant_j_swap
    (A B : ℚ) (hB : B ≠ 0) (hD : A ^ 2 - 4 * B ≠ 0) :
    xi_j_discriminant_2isogeny_discriminant_j_swap_sourceDiscriminant A B =
        2 ^ 4 * B ^ 2 * (A ^ 2 - 4 * B) ∧
      xi_j_discriminant_2isogeny_discriminant_j_swap_targetDiscriminant A B =
        2 ^ 8 * B * (A ^ 2 - 4 * B) ^ 2 ∧
      xi_j_discriminant_2isogeny_discriminant_j_swap_sourceJInvariant A B =
        256 * (A ^ 2 - 3 * B) ^ 3 / (B ^ 2 * (A ^ 2 - 4 * B)) ∧
      xi_j_discriminant_2isogeny_discriminant_j_swap_targetJInvariant A B =
        16 * (A ^ 2 + 12 * B) ^ 3 / (B * (A ^ 2 - 4 * B) ^ 2) ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ eB eD : ℕ,
        xi_j_discriminant_2isogeny_discriminant_j_swap_sourceOddExponent p eB eD =
          xi_j_discriminant_2isogeny_discriminant_j_swap_targetOddExponent p eD eB) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact xi_j_discriminant_2isogeny_discriminant_j_swap_source_discriminant_closed A B
  · exact xi_j_discriminant_2isogeny_discriminant_j_swap_target_discriminant_closed A B
  · rw [xi_j_discriminant_2isogeny_discriminant_j_swap_sourceJInvariant,
      xi_j_discriminant_2isogeny_discriminant_j_swap_jInvariant]
    change xi_j_discriminant_2isogeny_discriminant_j_swap_c4 A B ^ 3 /
        xi_j_discriminant_2isogeny_discriminant_j_swap_sourceDiscriminant A B =
      256 * (A ^ 2 - 3 * B) ^ 3 / (B ^ 2 * (A ^ 2 - 4 * B))
    rw [xi_j_discriminant_2isogeny_discriminant_j_swap_source_discriminant_closed]
    unfold xi_j_discriminant_2isogeny_discriminant_j_swap_c4
      xi_j_discriminant_2isogeny_discriminant_j_swap_b2
      xi_j_discriminant_2isogeny_discriminant_j_swap_b4
    field_simp [hB, hD]
    ring
  · rw [xi_j_discriminant_2isogeny_discriminant_j_swap_targetJInvariant,
      xi_j_discriminant_2isogeny_discriminant_j_swap_jInvariant]
    change xi_j_discriminant_2isogeny_discriminant_j_swap_c4 (-2 * A) (A ^ 2 - 4 * B) ^ 3 /
        xi_j_discriminant_2isogeny_discriminant_j_swap_targetDiscriminant A B =
      16 * (A ^ 2 + 12 * B) ^ 3 / (B * (A ^ 2 - 4 * B) ^ 2)
    rw [xi_j_discriminant_2isogeny_discriminant_j_swap_target_discriminant_closed]
    unfold xi_j_discriminant_2isogeny_discriminant_j_swap_c4
      xi_j_discriminant_2isogeny_discriminant_j_swap_b2
      xi_j_discriminant_2isogeny_discriminant_j_swap_b4
    field_simp [hB, hD]
    ring
  · intro p hp hpodd eB eD
    simp [xi_j_discriminant_2isogeny_discriminant_j_swap_sourceOddExponent,
      xi_j_discriminant_2isogeny_discriminant_j_swap_targetOddExponent, add_comm, mul_comm]

end

end Omega.Zeta
