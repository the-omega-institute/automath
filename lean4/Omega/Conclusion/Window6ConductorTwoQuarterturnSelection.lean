import Mathlib.Tactic

namespace Omega.Conclusion

/-- The three local hidden-template types are indexed by their support size. -/
inductive Window6LocalTemplate
  | two
  | three
  | four
  deriving DecidableEq, Repr

/-- The explicit local supports appearing in the window-6 analysis. -/
def window6TemplateSupport : Window6LocalTemplate → List ℕ
  | .two => [0, 34]
  | .three => [0, 21, 34]
  | .four => [0, 21, 34, 55]

/-- The conductor-2 Ramanujan character `c₂(n) = (-1)^n`. -/
def c2 (n : ℕ) : ℚ :=
  if n % 2 = 0 then 1 else -1

/-- The conductor-4 Ramanujan character `c₄(n) = i^n + (-i)^n`, recorded by its real value. -/
def c4 (n : ℕ) : ℚ :=
  match n % 4 with
  | 0 => 2
  | 1 => 0
  | 2 => -2
  | _ => 0

/-- Real part of the primitive quarter-turn character `χ₄(n) = i^n`. -/
def chi4Re (n : ℕ) : ℚ :=
  match n % 4 with
  | 0 => 1
  | 1 => 0
  | 2 => -1
  | _ => 0

/-- Imaginary part of the primitive quarter-turn character `χ₄(n) = i^n`. -/
def chi4Im (n : ℕ) : ℚ :=
  match n % 4 with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | _ => -1

/-- Uniform average of a rational-valued observable over a finite template. -/
def avgQ (support : List ℕ) (f : ℕ → ℚ) : ℚ :=
  (support.map f).sum / support.length

/-- Average of the primitive quarter-turn character, recorded as `(Re, Im)`. -/
def avgChi4 (T : Window6LocalTemplate) : ℚ × ℚ :=
  (avgQ (window6TemplateSupport T) chi4Re, avgQ (window6TemplateSupport T) chi4Im)

/-- The ordered pair that separates the three local template types. -/
def selectionPair (T : Window6LocalTemplate) : ℚ × ℚ :=
  (avgQ (window6TemplateSupport T) c2, avgQ (window6TemplateSupport T) chi4Im)

/-- Concrete package for the conductor-2 / primitive quarter-turn selection law. -/
def phaseSelectionLaw : Prop :=
  avgQ (window6TemplateSupport .two) c2 = 1 ∧
    avgQ (window6TemplateSupport .three) c2 = (1 : ℚ) / 3 ∧
      avgQ (window6TemplateSupport .four) c2 = 0 ∧
        avgQ (window6TemplateSupport .two) c4 = 0 ∧
          avgQ (window6TemplateSupport .three) c4 = 0 ∧
            avgQ (window6TemplateSupport .four) c4 = 0 ∧
              avgChi4 .two = (0, 0) ∧
                avgChi4 .three = (0, (1 : ℚ) / 3) ∧
                  avgChi4 .four = (0, 0) ∧
                    (∀ T, selectionPair T = (1, 0) ↔ T = .two) ∧
                      (∀ T, selectionPair T = ((1 : ℚ) / 3, (1 : ℚ) / 3) ↔ T = .three) ∧
                        (∀ T, selectionPair T = (0, 0) ↔ T = .four)

@[simp] theorem avgQ_support_two_c2 : avgQ (window6TemplateSupport .two) c2 = 1 := by
  norm_num [avgQ, window6TemplateSupport, c2]

@[simp] theorem avgQ_support_three_c2 : avgQ (window6TemplateSupport .three) c2 = (1 : ℚ) / 3 := by
  norm_num [avgQ, window6TemplateSupport, c2]

@[simp] theorem avgQ_support_four_c2 : avgQ (window6TemplateSupport .four) c2 = 0 := by
  norm_num [avgQ, window6TemplateSupport, c2]

@[simp] theorem avgQ_support_two_c4 : avgQ (window6TemplateSupport .two) c4 = 0 := by
  norm_num [avgQ, window6TemplateSupport, c4]

@[simp] theorem avgQ_support_three_c4 : avgQ (window6TemplateSupport .three) c4 = 0 := by
  norm_num [avgQ, window6TemplateSupport, c4]

@[simp] theorem avgQ_support_four_c4 : avgQ (window6TemplateSupport .four) c4 = 0 := by
  norm_num [avgQ, window6TemplateSupport, c4]

@[simp] theorem avgChi4_two : avgChi4 .two = (0, 0) := by
  norm_num [avgChi4, avgQ, window6TemplateSupport, chi4Re, chi4Im]

@[simp] theorem avgChi4_three : avgChi4 .three = (0, (1 : ℚ) / 3) := by
  norm_num [avgChi4, avgQ, window6TemplateSupport, chi4Re, chi4Im]

@[simp] theorem avgChi4_four : avgChi4 .four = (0, 0) := by
  norm_num [avgChi4, avgQ, window6TemplateSupport, chi4Re, chi4Im]

@[simp] theorem avgQ_support_two_chi4Im : avgQ (window6TemplateSupport .two) chi4Im = 0 := by
  norm_num [avgQ, window6TemplateSupport, chi4Im]

@[simp] theorem avgQ_support_three_chi4Im :
    avgQ (window6TemplateSupport .three) chi4Im = (1 : ℚ) / 3 := by
  norm_num [avgQ, window6TemplateSupport, chi4Im]

@[simp] theorem avgQ_support_four_chi4Im : avgQ (window6TemplateSupport .four) chi4Im = 0 := by
  norm_num [avgQ, window6TemplateSupport, chi4Im]

@[simp] theorem selectionPair_two : selectionPair .two = (1, 0) := by
  simp [selectionPair]

@[simp] theorem selectionPair_three : selectionPair .three = ((1 : ℚ) / 3, (1 : ℚ) / 3) := by
  simp [selectionPair]

@[simp] theorem selectionPair_four : selectionPair .four = (0, 0) := by
  simp [selectionPair]

/-- The conductor-2 averages, the conductor-4 averages, and the primitive quarter-turn averages
distinguish the `d(w) = 2, 3, 4` local templates exactly.
    thm:conclusion-window6-conductor-two-quarterturn-selection -/
theorem paper_conclusion_window6_conductor_two_quarterturn_selection :
    phaseSelectionLaw := by
  refine ⟨avgQ_support_two_c2, avgQ_support_three_c2, avgQ_support_four_c2, avgQ_support_two_c4,
    avgQ_support_three_c4, avgQ_support_four_c4, avgChi4_two, avgChi4_three, avgChi4_four, ?_,
    ?_, ?_⟩
  · intro T
    cases T <;> simp
  · intro T
    cases T <;> simp
  · intro T
    cases T <;> simp

end Omega.Conclusion
