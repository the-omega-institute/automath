import Mathlib.Tactic

namespace Omega.Conclusion

attribute [local instance] Classical.propDecidable

/-- Paper-local recurrence convention for the collision-moment halting-time transducer:
order `r = k + 1` means the sequence is constant from index `k` onward. -/
def collisionMomentTailOrder (seq : ℕ → ℕ) (r : ℕ) : Prop :=
  ∃ k, r = k + 1 ∧ ∀ n, seq (n + k) = seq (n + k + 1)

/-- Concrete halting-time data for the collision-moment sequence. The sequence is constant `2` in
the non-halting case and equals the explicit step profile `2` / `2^q` in the halting case. The
recorded minimal recurrence order is characterized against `collisionMomentTailOrder`. -/
structure CollisionMomentMinrecHaltingTimeData where
  halts : Prop
  haltingSteps : ℕ
  q : ℕ
  seq : ℕ → ℕ
  minRecurrenceOrder : ℕ
  nonhalting_seq : ¬ halts → seq = fun _ => 2
  halting_seq : halts → ∀ n, seq n = if n < haltingSteps then 2 else 2 ^ q
  halting_plateau_ne_two : halts → 0 < haltingSteps → 2 ^ q ≠ 2
  halting_power_ge_two : halts → 2 ≤ 2 ^ q
  min_order_spec : ∀ r, collisionMomentTailOrder seq r ↔ minRecurrenceOrder ≤ r

private theorem collisionMomentTailOrder_const_two :
    collisionMomentTailOrder (fun _ : ℕ => 2) 1 := by
  refine ⟨0, rfl, ?_⟩
  intro n
  rfl

private theorem minRecurrenceOrder_of_const
    {seq : ℕ → ℕ} {m : ℕ}
    (hseq : seq = fun _ => 2)
    (hspec : ∀ r, collisionMomentTailOrder seq r ↔ m ≤ r) :
    m = 1 := by
  have hm_le : m ≤ 1 := by
    have horder : collisionMomentTailOrder seq 1 := by simpa [hseq] using collisionMomentTailOrder_const_two
    exact (hspec 1).1 horder
  have hm_not_le_zero : ¬ m ≤ 0 := by
    intro hm0
    have horder0 : collisionMomentTailOrder seq 0 := (hspec 0).2 hm0
    rcases horder0 with ⟨k, hk, _⟩
    omega
  have hm_pos : 0 < m := by
    exact Nat.pos_of_ne_zero fun hm0 => hm_not_le_zero (hm0 ▸ le_rfl)
  exact le_antisymm hm_le (Nat.succ_le_of_lt hm_pos)

private theorem minRecurrenceOrder_of_halting
    {seq : ℕ → ℕ} {T q m : ℕ}
    (hseq : ∀ n, seq n = if n < T then 2 else 2 ^ q)
    (hgap : 0 < T → 2 ^ q ≠ 2)
    (hspec : ∀ r, collisionMomentTailOrder seq r ↔ m ≤ r) :
    m = T + 1 := by
  have hm_le : m ≤ T + 1 := by
    have horder : collisionMomentTailOrder seq (T + 1) := by
      refine ⟨T, rfl, ?_⟩
      intro n
      rw [hseq (n + T), hseq (n + T + 1)]
      have hleft : ¬ n + T < T := by omega
      have hright : ¬ n + T + 1 < T := by omega
      simp [hleft, hright]
    exact (hspec (T + 1)).1 horder
  have horder_min : collisionMomentTailOrder seq m := (hspec m).2 le_rfl
  have hm_ge : T + 1 ≤ m := by
    refine Nat.le_of_not_lt ?_
    intro hlt
    rcases horder_min with ⟨k, hk, hkconst⟩
    rw [hk] at hlt
    cases T with
    | zero =>
        omega
    | succ T =>
        have hconst_raw :
            seq (Nat.succ T - (k + 1) + k) = seq (Nat.succ T - (k + 1) + k + 1) :=
          hkconst (Nat.succ T - (k + 1))
        have hleft_eq : T - k + k = T := by omega
        have hright_eq : T - k + k + 1 = T + 1 := by omega
        have hconst' : seq T = seq (T + 1) := by
          simpa [hleft_eq, hright_eq] using hconst_raw
        rw [hseq T, hseq (T + 1)] at hconst'
        simp at hconst'
        exact (hgap (Nat.succ_pos _)) hconst'.symm
  exact le_antisymm hm_le hm_ge

/-- The collision-moment sequence for the halting-time transducer is constant `2` when the
machine does not halt, is the explicit step profile `2` / `2^q` when it halts at time `T`, and
the induced minimal tail-recurrence order is `1` in the non-halting case and `T + 1` in the
halting case.
    thm:conclusion-collision-moment-minrec-halting-time -/
theorem paper_conclusion_collision_moment_minrec_halting_time
    (h : CollisionMomentMinrecHaltingTimeData) :
    (¬ h.halts → h.seq = fun _ => 2) ∧
      (h.halts → ∀ n, h.seq n = if n < h.haltingSteps then 2 else 2 ^ h.q) ∧
      h.minRecurrenceOrder = if h.halts then h.haltingSteps + 1 else 1 := by
  refine ⟨h.nonhalting_seq, h.halting_seq, ?_⟩
  by_cases hh : h.halts
  · have hmin :=
      minRecurrenceOrder_of_halting (seq := h.seq) (T := h.haltingSteps) (q := h.q)
        (m := h.minRecurrenceOrder) (hseq := h.halting_seq hh)
        (hgap := h.halting_plateau_ne_two hh) (hspec := h.min_order_spec)
    simpa [hh] using hmin
  · have hmin :=
      minRecurrenceOrder_of_const (seq := h.seq) (m := h.minRecurrenceOrder)
        (hseq := h.nonhalting_seq hh) (hspec := h.min_order_spec)
    simpa [hh] using hmin

end Omega.Conclusion
