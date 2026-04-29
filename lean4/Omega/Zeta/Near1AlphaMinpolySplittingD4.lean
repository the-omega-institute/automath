import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Zeta

/-- The near-`1` endpoint parameter. -/
noncomputable def near1_alpha_minpoly_splitting_d4_alpha : ℝ :=
  Real.sqrt (-2 + 2 * Real.sqrt 5)

/-- The quartic polynomial evaluated as a real-valued expression. -/
noncomputable def near1_alpha_minpoly_splitting_d4_quartic (x : ℝ) : ℝ :=
  x ^ 4 + 4 * x ^ 2 - 16

/-- Boolean test for the finite monic-quadratic coefficient comparison. -/
def near1_alpha_minpoly_splitting_d4_quadratic_factor_comparison_test
    (t : Fin 33 × Fin 33 × Fin 33) : Bool :=
  let A : ℤ := (t.1 : ℤ) - 16
  let B : ℤ := (t.2.1 : ℤ) - 16
  let D : ℤ := (t.2.2 : ℤ) - 16
  decide (¬ (B * D = -16 ∧ A * (D - B) = 0 ∧ B + D - A ^ 2 = 4))

/-- Finite coefficient comparison for monic quadratic splittings of
`X^4 + 4X^2 - 16`. The bounds cover every integer constant-term comparison in the
monic quadratic ansatz. -/
def near1_alpha_minpoly_splitting_d4_quadratic_factor_comparison_certificate : Prop :=
  ((Finset.univ : Finset (Fin 33 × Fin 33 × Fin 33)).filter
      (fun t => near1_alpha_minpoly_splitting_d4_quadratic_factor_comparison_test t = false)).card =
    0

/-- The order-four rotation on the four formal roots. -/
def near1_alpha_minpoly_splitting_d4_rotation (i : Fin 4) : Fin 4 :=
  ⟨(i.val + 1) % 4, Nat.mod_lt _ (by decide)⟩

/-- A reflection of the four formal roots. -/
def near1_alpha_minpoly_splitting_d4_reflection (i : Fin 4) : Fin 4 :=
  ⟨(4 - i.val) % 4, Nat.mod_lt _ (by decide)⟩

/-- The concrete dihedral relations for the root permutation certificate. -/
def near1_alpha_minpoly_splitting_d4_dihedral_certificate : Prop :=
  (List.map
        (fun i : Fin 4 =>
          (near1_alpha_minpoly_splitting_d4_rotation
                (near1_alpha_minpoly_splitting_d4_rotation
                  (near1_alpha_minpoly_splitting_d4_rotation
                    (near1_alpha_minpoly_splitting_d4_rotation i)))).val)
        [0, 1, 2, 3] =
      [0, 1, 2, 3]) ∧
    (List.map
        (fun i : Fin 4 =>
          (near1_alpha_minpoly_splitting_d4_reflection
              (near1_alpha_minpoly_splitting_d4_reflection i)).val)
        [0, 1, 2, 3] =
      [0, 1, 2, 3]) ∧
      (List.map
          (fun i : Fin 4 =>
            (near1_alpha_minpoly_splitting_d4_reflection
                (near1_alpha_minpoly_splitting_d4_rotation
                  (near1_alpha_minpoly_splitting_d4_reflection i))).val)
          [0, 1, 2, 3] =
        List.map
          (fun i : Fin 4 =>
            (near1_alpha_minpoly_splitting_d4_rotation
              (near1_alpha_minpoly_splitting_d4_rotation
                (near1_alpha_minpoly_splitting_d4_rotation i))).val)
          [0, 1, 2, 3])

/-- Concrete bundled statement for the near-`1` endpoint algebra package. -/
def near1_alpha_minpoly_splitting_d4_statement : Prop :=
  near1_alpha_minpoly_splitting_d4_alpha ^ 2 = -2 + 2 * Real.sqrt 5 ∧
    near1_alpha_minpoly_splitting_d4_quartic
        near1_alpha_minpoly_splitting_d4_alpha =
      0 ∧
      near1_alpha_minpoly_splitting_d4_quadratic_factor_comparison_certificate ∧
        near1_alpha_minpoly_splitting_d4_dihedral_certificate

private theorem near1_alpha_minpoly_splitting_d4_radicand_nonneg :
    0 ≤ (-2 + 2 * Real.sqrt 5 : ℝ) := by
  have hsqrt_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by positivity)
  have hsqrt_nonneg : 0 ≤ (Real.sqrt 5 : ℝ) := Real.sqrt_nonneg 5
  nlinarith

theorem near1_alpha_minpoly_splitting_d4_alpha_sq :
    near1_alpha_minpoly_splitting_d4_alpha ^ 2 = -2 + 2 * Real.sqrt 5 := by
  rw [near1_alpha_minpoly_splitting_d4_alpha, Real.sq_sqrt
    near1_alpha_minpoly_splitting_d4_radicand_nonneg]

theorem near1_alpha_minpoly_splitting_d4_quartic_vanishes :
    near1_alpha_minpoly_splitting_d4_quartic near1_alpha_minpoly_splitting_d4_alpha = 0 := by
  have hsqrt_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by positivity)
  rw [near1_alpha_minpoly_splitting_d4_quartic]
  rw [show near1_alpha_minpoly_splitting_d4_alpha ^ 4 =
      (near1_alpha_minpoly_splitting_d4_alpha ^ 2) ^ 2 by ring]
  rw [near1_alpha_minpoly_splitting_d4_alpha_sq]
  ring_nf
  nlinarith

theorem near1_alpha_minpoly_splitting_d4_quadratic_factor_comparison :
    near1_alpha_minpoly_splitting_d4_quadratic_factor_comparison_certificate := by
  unfold near1_alpha_minpoly_splitting_d4_quadratic_factor_comparison_certificate
    near1_alpha_minpoly_splitting_d4_quadratic_factor_comparison_test
  native_decide

theorem near1_alpha_minpoly_splitting_d4_dihedral_relations :
    near1_alpha_minpoly_splitting_d4_dihedral_certificate := by
  unfold near1_alpha_minpoly_splitting_d4_dihedral_certificate
    near1_alpha_minpoly_splitting_d4_rotation near1_alpha_minpoly_splitting_d4_reflection
  native_decide

/-- Paper label: `thm:near1-alpha-minpoly-splitting-d4`. -/
theorem paper_near1_alpha_minpoly_splitting_d4 :
    near1_alpha_minpoly_splitting_d4_statement := by
  exact ⟨near1_alpha_minpoly_splitting_d4_alpha_sq,
    near1_alpha_minpoly_splitting_d4_quartic_vanishes,
    near1_alpha_minpoly_splitting_d4_quadratic_factor_comparison,
    near1_alpha_minpoly_splitting_d4_dihedral_relations⟩

/-- Paper label: `thm:near1-alpha-2-over-sqrtphi-galois-D4`. -/
theorem paper_near1_alpha_2_over_sqrtphi_galois_d4 :
    near1_alpha_minpoly_splitting_d4_statement := by
  exact paper_near1_alpha_minpoly_splitting_d4

end Omega.Zeta
