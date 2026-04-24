import Mathlib.Tactic

namespace Omega.Zeta

/-- Minimal atomic data stream attached to a halting certificate. When `haltsAt = some t`, the
stream emits exactly one atom at time `t`; when `haltsAt = none`, it stays empty. -/
def operator_fredholm_zeta_equality_undecidable_atomic_stream
    (haltsAt : Option ℕ) : ℕ → Option (ℚ × ℕ × ℕ)
  | t =>
      if haltsAt = some t then
        some ((1 : ℚ) / 2 ^ (t + 1), t + 1, 1)
      else
        none

/-- Minimal Fredholm-zeta seed attached to the same halting certificate. The non-halting branch is
the constant `1`, while the halting branch inserts a single positive monomial correction. -/
def operator_fredholm_zeta_equality_undecidable_fredholm_zeta
    (haltsAt : Option ℕ) : ℚ → ℚ
  | r =>
      match haltsAt with
      | none => 1
      | some t => 1 + ((1 : ℚ) / 2 ^ (t + 1)) * r ^ (t + 1)

/-- Paper label: `thm:operator-fredholm-zeta-equality-undecidable`.
This concrete reduction seed isolates the key halting criterion: the attached Fredholm zeta is
identically `1` exactly in the non-halting case, and the atomic stream is empty exactly in the
same case. -/
theorem paper_operator_fredholm_zeta_equality_undecidable
    (haltsAt : Option ℕ) :
    ((operator_fredholm_zeta_equality_undecidable_fredholm_zeta haltsAt =
          fun _ => (1 : ℚ)) ↔
        haltsAt = none) ∧
      ((operator_fredholm_zeta_equality_undecidable_atomic_stream haltsAt =
            operator_fredholm_zeta_equality_undecidable_atomic_stream none) ↔
        haltsAt = none) := by
  cases haltsAt with
  | none =>
      refine ⟨?_, ?_⟩
      · constructor
        · intro _
          rfl
        · intro _
          funext r
          simp [operator_fredholm_zeta_equality_undecidable_fredholm_zeta]
      · constructor
        · intro _
          rfl
        · intro _
          rfl
  | some t =>
      refine ⟨?_, ?_⟩
      · constructor
        · intro hz
          have h1 := congrArg (fun f : ℚ → ℚ => f 1) hz
          simp [operator_fredholm_zeta_equality_undecidable_fredholm_zeta] at h1
        · intro h
          cases h
      · constructor
        · intro hs
          have hvalue :
              some ((1 : ℚ) / 2 ^ (t + 1), t + 1, 1) = none := by
            have this := congrArg (fun f : ℕ → Option (ℚ × ℕ × ℕ) => f t) hs
            simp [operator_fredholm_zeta_equality_undecidable_atomic_stream] at this
          cases hvalue
        · intro h
          cases h

end Omega.Zeta
