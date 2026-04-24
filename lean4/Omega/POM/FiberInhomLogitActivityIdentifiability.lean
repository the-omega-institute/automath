import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

private def activityPair (m : ℕ) (w : Fin (m - 2) → ℝ) (a1 a2 : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a1, a2)
  | n + 1 =>
      let p := activityPair m w a1 a2 n
      (p.2, if h : n < m - 2 then w ⟨n, h⟩ * p.1 / p.2 else 0)

private def activitySeqNat (m : ℕ) (w : Fin (m - 2) → ℝ) (a1 a2 : ℝ) : ℕ → ℝ
  | 0 => a1
  | n + 1 => (activityPair m w a1 a2 n).2

private lemma activityPair_fst_eq_activitySeqNat (m : ℕ) (w : Fin (m - 2) → ℝ) (a1 a2 : ℝ) :
    ∀ n, (activityPair m w a1 a2 n).1 = activitySeqNat m w a1 a2 n
  | 0 => rfl
  | n + 1 => by
      simp [activityPair, activitySeqNat, activityPair_fst_eq_activitySeqNat]

private lemma activitySeqNat_step (m : ℕ) (w : Fin (m - 2) → ℝ) (a1 a2 : ℝ) (n : ℕ)
    (hn : n < m - 2) :
    activitySeqNat m w a1 a2 (n + 2) =
      w ⟨n, hn⟩ * activitySeqNat m w a1 a2 n / activitySeqNat m w a1 a2 (n + 1) := by
  simp [activitySeqNat, activityPair, hn, activityPair_fst_eq_activitySeqNat]

private lemma solution_eq_activitySeqNat (m : ℕ) (hm : 2 ≤ m) (w : Fin (m - 2) → ℝ) (a1 a2 : ℝ)
    (a : Fin m → ℝ) (ha0 : a ⟨0, by omega⟩ = a1) (ha1 : a ⟨1, by omega⟩ = a2)
    (hrec : ∀ i : Fin (m - 2),
      a ⟨i.1 + 2, by omega⟩ = w i * a ⟨i.1, by omega⟩ / a ⟨i.1 + 1, by omega⟩) :
    ∀ n (hn : n < m), a ⟨n, hn⟩ = activitySeqNat m w a1 a2 n := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih hn
  cases n with
  | zero =>
      simpa [activitySeqNat] using ha0
  | succ n =>
      cases n with
      | zero =>
          simpa [activitySeqNat, activityPair] using ha1
      | succ k =>
          have hk : k < m - 2 := by omega
          have hk0 : k < m := by omega
          have hk1 : k + 1 < m := by omega
          have hEq0 : a ⟨k, by omega⟩ = activitySeqNat m w a1 a2 k := by
            simpa using ih k (by omega) hk0
          have hEq1 : a ⟨k + 1, by omega⟩ = activitySeqNat m w a1 a2 (k + 1) := by
            simpa using ih (k + 1) (by omega) hk1
          calc
            a ⟨k + 2, by omega⟩ = w ⟨k, hk⟩ * a ⟨k, by omega⟩ / a ⟨k + 1, by omega⟩ := by
              simpa using hrec ⟨k, hk⟩
            _ = w ⟨k, hk⟩ * activitySeqNat m w a1 a2 k / activitySeqNat m w a1 a2 (k + 1) := by
              rw [hEq0, hEq1]
            _ = activitySeqNat m w a1 a2 (k + 2) := by
              symm
              exact activitySeqNat_step m w a1 a2 k hk

/-- Given positive local activities `w_i = a_i a_{i+2} / a_{i+1}`, the corrected finite-prefix
recurrence uniquely reconstructs the finite activity vector from the boundary values `a₁,a₂`.
    prop:pom-inhom-logit-activity-identifiability -/
theorem paper_pom_inhom_logit_activity_identifiability (m : ℕ) (hm : 2 ≤ m)
    (w : Fin (m - 2) → ℝ) (a1 a2 : ℝ) (hw : ∀ i, 0 < w i) (ha1 : 0 < a1) (ha2 : 0 < a2) :
    ∃! a : Fin m → ℝ,
      a ⟨0, by omega⟩ = a1 ∧
      a ⟨1, by omega⟩ = a2 ∧
      (∀ i : Fin (m - 2),
        a ⟨i.1 + 2, by omega⟩ = w i * a ⟨i.1, by omega⟩ / a ⟨i.1 + 1, by omega⟩) := by
  let _ := hw
  let _ := ha1
  let _ := ha2
  let a : Fin m → ℝ := fun i => activitySeqNat m w a1 a2 i.1
  refine ⟨a, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp [a, activitySeqNat]
    · simp [a, activitySeqNat, activityPair]
    · intro i
      simpa [a] using activitySeqNat_step m w a1 a2 i.1 i.2
  · intro b hb
    rcases hb with ⟨hb0, hb1, hbrec⟩
    funext i
    exact solution_eq_activitySeqNat m hm w a1 a2 b hb0 hb1 hbrec i.1 i.2

end

end Omega.POM
