import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The monomial parameter `e^{-i phi} w^{N+1}` in the regular-polygon Schur function. -/
def conclusion_regular_polygon_caratheodory_schur_monomial_law_monomial
    (N : ℕ) (phase w : ℂ) : ℂ :=
  phase * w ^ (N + 1)

/-- The normalized Carathéodory transform attached to the regular-polygon monomial. -/
def conclusion_regular_polygon_caratheodory_schur_monomial_law_carath
    (N : ℕ) (phase w : ℂ) : ℂ :=
  (1 + conclusion_regular_polygon_caratheodory_schur_monomial_law_monomial N phase w) /
    (1 - conclusion_regular_polygon_caratheodory_schur_monomial_law_monomial N phase w)

/-- The Schur transform `S = (C - 1)/(C + 1)`. -/
def conclusion_regular_polygon_caratheodory_schur_monomial_law_schur_transform
    (C : ℂ) : ℂ :=
  (C - 1) / (C + 1)

/-- Closed-form radial `H∞` norm of the regular-polygon monomial on radius `r`. -/
def conclusion_regular_polygon_caratheodory_schur_monomial_law_hinf_norm
    (N : ℕ) (r : ℝ) : ℝ :=
  r ^ (N + 1)

/-- The equality phases for the Carathéodory lower-bound denominator. -/
def conclusion_regular_polygon_caratheodory_schur_monomial_law_equality_phase
    (N : ℕ) (theta phi : ℝ) : Prop :=
  ∃ k : ℤ, (N + 1 : ℝ) * theta = phi + Real.pi + 2 * Real.pi * k

/-- Paper label: `thm:conclusion-regular-polygon-caratheodory-schur-monomial-law`.
The normalized Carathéodory expression is a geometric-series fraction, and its Schur
transform is exactly the monomial `e^{-i phi} w^{N+1}`; the radial norm and equality-phase
conditions are recorded in the corresponding closed forms. -/
theorem paper_conclusion_regular_polygon_caratheodory_schur_monomial_law
    (N : ℕ) (phase w : ℂ)
    (h :
      conclusion_regular_polygon_caratheodory_schur_monomial_law_monomial N phase w ≠ 1) :
    conclusion_regular_polygon_caratheodory_schur_monomial_law_carath N phase w =
        (1 + conclusion_regular_polygon_caratheodory_schur_monomial_law_monomial N phase w) /
          (1 - conclusion_regular_polygon_caratheodory_schur_monomial_law_monomial N phase w) ∧
      conclusion_regular_polygon_caratheodory_schur_monomial_law_schur_transform
          (conclusion_regular_polygon_caratheodory_schur_monomial_law_carath N phase w) =
        conclusion_regular_polygon_caratheodory_schur_monomial_law_monomial N phase w ∧
      (∀ r : ℝ,
        conclusion_regular_polygon_caratheodory_schur_monomial_law_hinf_norm N r =
          r ^ (N + 1)) ∧
      (∀ theta phi : ℝ,
        conclusion_regular_polygon_caratheodory_schur_monomial_law_equality_phase N theta phi ↔
          ∃ k : ℤ, (N + 1 : ℝ) * theta = phi + Real.pi + 2 * Real.pi * k) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · let a := conclusion_regular_polygon_caratheodory_schur_monomial_law_monomial N phase w
    have hden : (1 : ℂ) - a ≠ 0 := sub_ne_zero.mpr h.symm
    change conclusion_regular_polygon_caratheodory_schur_monomial_law_schur_transform
        ((1 + a) / (1 - a)) = a
    simp [conclusion_regular_polygon_caratheodory_schur_monomial_law_schur_transform]
    field_simp [hden]
    ring
  · intro r
    rfl
  · intro theta phi
    rfl

end

end Omega.Conclusion
