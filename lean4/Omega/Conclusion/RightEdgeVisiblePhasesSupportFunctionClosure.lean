import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

def conclusion_right_edge_visible_phases_support_function_closure_affine
    (alphaStar : Real) (phase : Real × Real) (a : Real) : Real :=
  phase.2 - a * (alphaStar - phase.1)

def conclusion_right_edge_visible_phases_support_function_closure_R
    (alphaStar : Real) (phases : List (Real × Real)) (a : Real) : Real :=
  phases.foldr
    (fun phase acc =>
      max (conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase a)
        acc)
    0

def conclusion_right_edge_visible_phases_support_function_closure_crossover_scale
    (p q : Real × Real) : Real :=
  (q.2 - p.2) / (p.1 - q.1)

def conclusion_right_edge_visible_phases_support_function_closure_statement
    (alphaStar : Real) (phases : List (Real × Real)) : Prop :=
  (∀ a,
      conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases a =
        phases.foldr
          (fun phase acc =>
            max
              (conclusion_right_edge_visible_phases_support_function_closure_affine
                alphaStar phase a)
              acc)
          0) ∧
    (∀ x y,
      conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases
          ((x + y) / 2) ≤
        (conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases x +
            conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases y) /
          2) ∧
    (∀ a,
      ∃ phase ∈ (alphaStar, 0) :: phases,
        conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases a =
          conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase a) ∧
    ((∀ phase ∈ phases, phase.1 ≤ alphaStar) →
      ∀ ⦃a₁ a₂⦄, a₁ ≤ a₂ →
        conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases a₂ ≤
          conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases a₁) ∧
    (∀ p q,
      p ∈ (alphaStar, 0) :: phases →
      q ∈ (alphaStar, 0) :: phases →
      p.1 ≠ q.1 →
        let a :=
          conclusion_right_edge_visible_phases_support_function_closure_crossover_scale p q
        conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar p a =
          conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar q a)

lemma conclusion_right_edge_visible_phases_support_function_closure_affine_midpoint
    (alphaStar : Real) (phase : Real × Real) (x y : Real) :
    conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase
        ((x + y) / 2) =
      (conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase x +
          conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase y) /
        2 := by
  unfold conclusion_right_edge_visible_phases_support_function_closure_affine
  ring

lemma conclusion_right_edge_visible_phases_support_function_closure_R_midpoint_convex
    (alphaStar : Real) (phases : List (Real × Real)) (x y : Real) :
    conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases
        ((x + y) / 2) ≤
      (conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases x +
          conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases y) /
        2 := by
  induction phases with
  | nil =>
      simp [conclusion_right_edge_visible_phases_support_function_closure_R]
  | cons phase phases ih =>
      have hphase :
          conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase
              ((x + y) / 2) =
            (conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar
                  phase x +
                conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar
                  phase y) /
              2 :=
        conclusion_right_edge_visible_phases_support_function_closure_affine_midpoint alphaStar
          phase x y
      have hleft :
          conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase
              ((x + y) / 2) ≤
            (max
                  (conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar
                    phase x)
                  (conclusion_right_edge_visible_phases_support_function_closure_R alphaStar
                    phases x) +
                max
                  (conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar
                    phase y)
                  (conclusion_right_edge_visible_phases_support_function_closure_R alphaStar
                    phases y)) /
              2 := by
        rw [hphase]
        have hx :
            conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase
                x ≤
              max
                (conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar
                  phase x)
                (conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases x) :=
          le_max_left _ _
        have hy :
            conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase
                y ≤
              max
                (conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar
                  phase y)
                (conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases y) :=
          le_max_left _ _
        linarith
      have hright :
          conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases
              ((x + y) / 2) ≤
            (max
                  (conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar
                    phase x)
                  (conclusion_right_edge_visible_phases_support_function_closure_R alphaStar
                    phases x) +
                max
                  (conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar
                    phase y)
                  (conclusion_right_edge_visible_phases_support_function_closure_R alphaStar
                    phases y)) /
              2 := by
        have hx :
            conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases x ≤
              max
                (conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar
                  phase x)
                (conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases x) :=
          le_max_right _ _
        have hy :
            conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases y ≤
              max
                (conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar
                  phase y)
                (conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases y) :=
          le_max_right _ _
        linarith [ih, hx, hy]
      refine (max_le_iff.mpr ⟨hleft, hright⟩).trans ?_
      rfl

lemma conclusion_right_edge_visible_phases_support_function_closure_R_piecewise
    (alphaStar : Real) (phases : List (Real × Real)) (a : Real) :
    ∃ phase ∈ (alphaStar, 0) :: phases,
      conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases a =
        conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase a := by
  induction phases with
  | nil =>
      refine ⟨(alphaStar, 0), by simp, ?_⟩
      simp [conclusion_right_edge_visible_phases_support_function_closure_R,
        conclusion_right_edge_visible_phases_support_function_closure_affine]
  | cons phase phases ih =>
      by_cases hphase :
          conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases a ≤
            conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase a
      · refine ⟨phase, by simp, ?_⟩
        change
          max
              (conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar
                phase a)
              (conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases a) =
            conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase a
        exact max_eq_left hphase
      · rcases ih with ⟨chosen, hchosen, hchosenEq⟩
        refine ⟨chosen, ?_, ?_⟩
        have hmem : chosen = phase ∨ chosen = (alphaStar, 0) ∨ chosen ∈ phases := by
          simp [List.mem_cons] at hchosen
          rcases hchosen with hbase | htail
          · exact Or.inr (Or.inl hbase)
          · exact Or.inr (Or.inr htail)
        simpa [List.mem_cons, or_assoc, or_left_comm, or_comm] using hmem
        have hle :
            conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase a ≤
              conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases a :=
          le_of_not_ge hphase
        have hle' :
            conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase a ≤
              conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar
                chosen a := by
          rwa [hchosenEq] at hle
        have hmax :
            max
                (conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar
                  phase a)
                (conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar
                  chosen a) =
              conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar
                chosen a :=
          max_eq_right hle'
        change
          max
              (conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar
                phase a)
              (conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases a) =
            conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar chosen a
        rw [hchosenEq]
        exact hmax

lemma conclusion_right_edge_visible_phases_support_function_closure_affine_antitone
    {alphaStar : Real} {phase : Real × Real} {a₁ a₂ : Real} (hphase : phase.1 ≤ alphaStar)
    (ha : a₁ ≤ a₂) :
    conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase a₂ ≤
      conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase a₁ := by
  unfold conclusion_right_edge_visible_phases_support_function_closure_affine
  have hslope : 0 ≤ alphaStar - phase.1 := sub_nonneg.mpr hphase
  have hmul : a₁ * (alphaStar - phase.1) ≤ a₂ * (alphaStar - phase.1) :=
    mul_le_mul_of_nonneg_right ha hslope
  linarith

lemma conclusion_right_edge_visible_phases_support_function_closure_R_antitone
    {alphaStar : Real} {phases : List (Real × Real)} {a₁ a₂ : Real}
    (hphases : ∀ phase ∈ phases, phase.1 ≤ alphaStar) (ha : a₁ ≤ a₂) :
    conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases a₂ ≤
      conclusion_right_edge_visible_phases_support_function_closure_R alphaStar phases a₁ := by
  induction phases with
  | nil =>
      simp [conclusion_right_edge_visible_phases_support_function_closure_R]
  | cons phase phases ih =>
      have hphase : phase.1 ≤ alphaStar := hphases phase (by simp)
      have htail : ∀ p ∈ phases, p.1 ≤ alphaStar := by
        intro p hp
        exact hphases p (by simp [hp])
      have hphaseMono :
          conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase a₂ ≤
            conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar phase a₁ :=
        conclusion_right_edge_visible_phases_support_function_closure_affine_antitone hphase ha
      exact max_le_max hphaseMono (ih htail)

lemma conclusion_right_edge_visible_phases_support_function_closure_affine_crossover
    (alphaStar : Real) (p q : Real × Real) (hpq : p.1 ≠ q.1) :
    let a := conclusion_right_edge_visible_phases_support_function_closure_crossover_scale p q
    conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar p a =
      conclusion_right_edge_visible_phases_support_function_closure_affine alphaStar q a := by
  have hpq' : p.1 - q.1 ≠ 0 := sub_ne_zero.mpr hpq
  unfold conclusion_right_edge_visible_phases_support_function_closure_crossover_scale
    conclusion_right_edge_visible_phases_support_function_closure_affine
  field_simp [hpq']
  ring_nf

/-- Paper label: `thm:conclusion-right-edge-visible-phases-support-function-closure`.
For a finite visible phase list, the right-edge support correction is the maximum of the visible
affine branches; it is midpoint-convex, realized by one visible phase or the zero baseline,
monotone when all visible slopes point left, and each pair of branches crosses at the expected
scale. -/
theorem paper_conclusion_right_edge_visible_phases_support_function_closure
    (alphaStar : Real) (phases : List (Real × Real)) :
    conclusion_right_edge_visible_phases_support_function_closure_statement alphaStar phases := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rfl
  · intro x y
    exact
      conclusion_right_edge_visible_phases_support_function_closure_R_midpoint_convex alphaStar
        phases x y
  · intro a
    exact
      conclusion_right_edge_visible_phases_support_function_closure_R_piecewise alphaStar phases a
  · intro hphases a₁ a₂ ha
    exact
      conclusion_right_edge_visible_phases_support_function_closure_R_antitone hphases ha
  · intro p q hp hq hpq
    exact
      conclusion_right_edge_visible_phases_support_function_closure_affine_crossover alphaStar p q
        hpq

end

end Omega.Conclusion
