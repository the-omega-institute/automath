import Mathlib.Tactic
import Omega.Discussion.ChebyshevAdams

namespace Omega.Discussion

/-- Rational Chebyshev-Adams recurrence on the Cayley coordinate. -/
def chebyAdamsRat : ℕ → ℚ → ℚ
  | 0, _ => 2
  | 1, S => S
  | n + 2, S => S * chebyAdamsRat (n + 1) S - chebyAdamsRat n S

/-- The Cayley coordinate used in the audit discussion. -/
def auditCayleyS (x : ℚ) : ℚ :=
  2 * (1 - x ^ 2) / (1 + x ^ 2)

/-- Recursive numerator/denominator pair for the rational substitutions `τ_d(x)`. The recurrence is
the tangent-angle addition law written in integer-polynomial arithmetic. -/
def auditTauPair : ℕ → ℚ → ℚ × ℚ
  | 0, _ => (0, 1)
  | n + 1, x =>
      let p := auditTauPair n x
      (p.1 + x * p.2, p.2 - x * p.1)

def auditTauNum (n : ℕ) (x : ℚ) : ℚ := (auditTauPair n x).1
def auditTauDen (n : ℕ) (x : ℚ) : ℚ := (auditTauPair n x).2

/-- The Cayley expression attached to a numerator/denominator pair. -/
def auditRaw (num den : ℚ) : ℚ :=
  2 * (den ^ 2 - num ^ 2) / (den ^ 2 + num ^ 2)

/-- The Cayley image of the rational map `τ_n(x) = num / den`, written without introducing a
division by `auditTauDen n x`. -/
def auditClosedForm (n : ℕ) (x : ℚ) : ℚ :=
  auditRaw (auditTauNum n x) (auditTauDen n x)

@[simp] lemma auditTauNum_zero (x : ℚ) : auditTauNum 0 x = 0 := rfl
@[simp] lemma auditTauDen_zero (x : ℚ) : auditTauDen 0 x = 1 := rfl

@[simp] lemma auditTauNum_succ (n : ℕ) (x : ℚ) :
    auditTauNum (n + 1) x = auditTauNum n x + x * auditTauDen n x := by
  cases h : auditTauPair n x with
  | mk num den =>
      simp [auditTauNum, auditTauDen, auditTauPair, h]

@[simp] lemma auditTauDen_succ (n : ℕ) (x : ℚ) :
    auditTauDen (n + 1) x = auditTauDen n x - x * auditTauNum n x := by
  cases h : auditTauPair n x with
  | mk num den =>
      simp [auditTauNum, auditTauDen, auditTauPair, h]

@[simp] lemma auditTauNum_one (x : ℚ) : auditTauNum 1 x = x := by
  simp

@[simp] lemma auditTauDen_one (x : ℚ) : auditTauDen 1 x = 1 := by
  simp

lemma auditTauNum_two (x : ℚ) : auditTauNum 2 x = 2 * x := by
  simp [auditTauNum_succ]
  ring

lemma auditTauDen_two (x : ℚ) : auditTauDen 2 x = 1 - x ^ 2 := by
  simp [auditTauDen_succ]
  ring

lemma auditTauNum_three (x : ℚ) : auditTauNum 3 x = 3 * x - x ^ 3 := by
  rw [auditTauNum_succ, auditTauNum_two, auditTauDen_two]
  ring

lemma auditTauDen_three (x : ℚ) : auditTauDen 3 x = 1 - 3 * x ^ 2 := by
  rw [auditTauDen_succ, auditTauDen_two, auditTauNum_two]
  ring

@[simp] lemma auditClosedForm_zero (x : ℚ) : auditClosedForm 0 x = 2 := by
  simp [auditClosedForm, auditRaw]

@[simp] lemma auditClosedForm_one (x : ℚ) : auditClosedForm 1 x = auditCayleyS x := by
  simp [auditClosedForm, auditRaw, auditCayleyS]

lemma chebyAdamsRat_two (S : ℚ) : chebyAdamsRat 2 S = S ^ 2 - 2 := by
  simp [chebyAdamsRat]
  ring

lemma chebyAdamsRat_three (S : ℚ) : chebyAdamsRat 3 S = S ^ 3 - 3 * S := by
  simp [chebyAdamsRat]
  ring

/-- The first nontrivial Cayley certificate substitutions already close inside integer-polynomial
numerator/denominator arithmetic over `x`.
    cor:discussion-audit-closure-Zx -/
theorem paper_discussion_audit_closure_zx (x : ℚ) :
    auditTauNum 1 x = x ∧
      auditTauDen 1 x = 1 ∧
      auditTauNum 2 x = 2 * x ∧
      auditTauDen 2 x = 1 - x ^ 2 ∧
      auditTauNum 3 x = 3 * x - x ^ 3 ∧
      auditTauDen 3 x = 1 - 3 * x ^ 2 ∧
      auditClosedForm 1 x = auditCayleyS x := by
  refine ⟨auditTauNum_one x, auditTauDen_one x, auditTauNum_two x, auditTauDen_two x,
    auditTauNum_three x, auditTauDen_three x, auditClosedForm_one x⟩

end Omega.Discussion
