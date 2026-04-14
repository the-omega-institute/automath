import Omega.Folding.EndpointUnique
import Omega.Folding.HammingDist
import Omega.Folding.MaxFiber

namespace Omega.Folding.EndpointMmMinusOneUnique

/-- The unique stable endpoint word of weight `F_{m+2} - 1`. -/
def endpointWord : (m : ℕ) → Word m
  | 0 => fun i => False.elim (Nat.not_lt_zero _ i.isLt)
  | 1 => fun _ => true
  | m + 2 => snoc (snoc (endpointWord m) false) true

private theorem fib_endpoint_step (m : ℕ) :
    Nat.fib (m + 4) - 1 = (Nat.fib (m + 2) - 1) + Nat.fib (m + 3) := by
  have hfib : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (Nat.fib_add_two (n := m + 2))
  have hpos : 0 < Nat.fib (m + 2) := fib_succ_pos (m + 1)
  omega

theorem endpointWord_no11 : ∀ m, No11 (endpointWord m)
  | 0 => by
      simpa [endpointWord] using (no11_allFalse : No11 (fun _ : Fin 0 => false))
  | 1 => by
      intro i hi hi1
      have : ¬ i + 1 < 1 := by omega
      simp [get, this] at hi1
  | m + 2 => by
      simpa [endpointWord] using
        no11_snoc_true (no11_snoc_false (endpointWord_no11 m)) (by simp)

theorem endpointWord_weight : ∀ m, weight (endpointWord m) = Nat.fib (m + 2) - 1
  | 0 => by simp [endpointWord]
  | 1 => by norm_num [endpointWord, weight]
  | m + 2 => by
      simp [endpointWord, endpointWord_weight m, fib_endpoint_step]

theorem weight_le_endpointWord : ∀ {m : ℕ} (w : Word m), No11 w → weight w ≤ Nat.fib (m + 2) - 1
  | 0, w, _ => by
      have hw0 : weight w = 0 := by simp [weight]
      rw [hw0]
      norm_num
  | 1, w, _ => by
      rw [weight_word_one]
      split <;> norm_num
  | m + 2, w, hwNo11 => by
      cases hLast : w ⟨m + 1, by omega⟩ with
      | false =>
          have htr := weight_le_endpointWord (truncate w) (no11_truncate hwNo11)
          rw [weight_of_lastFalse hLast]
          have hmono : Nat.fib (m + 3) - 1 ≤ Nat.fib (m + 4) - 1 := by
            exact Nat.sub_le_sub_right (Nat.fib_mono (by omega)) 1
          exact le_trans htr hmono
      | true =>
          have hPrevFalse : w ⟨m, by omega⟩ = false := by
            by_contra hPrev
            have hPrevGet : get w m = true := by simpa [get] using hPrev
            have hLastGet : get w (m + 1) = true := by simpa [get] using hLast
            exact hwNo11 m hPrevGet hLastGet
          have htr :=
            weight_le_endpointWord (truncate (truncate w)) (no11_truncate (no11_truncate hwNo11))
          have hmid : weight (truncate w) = weight (truncate (truncate w)) := by
            apply weight_of_lastFalse
            simpa [truncate] using hPrevFalse
          rw [weight_of_lastTrue hLast, hmid, fib_endpoint_step]
          exact Nat.add_le_add_right htr _

set_option maxHeartbeats 400000 in
theorem endpointWord_unique : ∀ {m : ℕ} (w : Word m),
    No11 w → weight w = Nat.fib (m + 2) - 1 → w = endpointWord m
  | 0, w, _, hw => by
      have hw0 : weight w = 0 := by simpa using hw
      calc
        w = fun _ : Fin 0 => false := (weight_zero_iff_allFalse w).mp hw0
        _ = endpointWord 0 := by
          funext i
          exact False.elim (Nat.not_lt_zero _ i.isLt)
  | 1, w, _, hw => by
      have hbit : w ⟨0, Nat.zero_lt_one⟩ = true := by
        have hpos : 0 < weight w := by
          have : weight w = 1 := by simpa using hw
          omega
        rcases (weight_pos_iff_exists_true w).mp hpos with ⟨i, hi⟩
        have : i = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by omega)
        simpa [this] using hi
      funext i
      have : i = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by omega)
      subst this
      simpa [endpointWord] using hbit
  | m + 2, w, hwNo11, hw => by
      have hLastTrue : w ⟨m + 1, by omega⟩ = true := by
        cases hLast : w ⟨m + 1, by omega⟩ with
        | false =>
            have hle := weight_le_endpointWord (truncate w) (no11_truncate hwNo11)
            rw [weight_of_lastFalse hLast] at hw
            have hlt : Nat.fib (m + 3) - 1 < Nat.fib (m + 4) - 1 := by
              rw [fib_endpoint_step]
              have hlt1 : Nat.fib (m + 3) - 1 < Nat.fib (m + 3) := by
                have hpos3 : 0 < Nat.fib (m + 3) := fib_succ_pos (m + 2)
                omega
              have hle2 : Nat.fib (m + 3) ≤ (Nat.fib (m + 2) - 1) + Nat.fib (m + 3) := by
                omega
              exact lt_of_lt_of_le hlt1 hle2
            have : Nat.fib (m + 4) - 1 ≤ Nat.fib (m + 3) - 1 := by
              simpa [hw] using hle
            exact False.elim ((Nat.not_le_of_lt hlt) this)
        | true => rfl
      have hPrevFalse : w ⟨m, by omega⟩ = false := by
        by_contra hPrev
        have hPrevGet : get w m = true := by simpa [get] using hPrev
        have hLastGet : get w (m + 1) = true := by simpa [get] using hLastTrue
        exact hwNo11 m hPrevGet hLastGet
      have hmid : weight (truncate w) = weight (truncate (truncate w)) := by
        apply weight_of_lastFalse
        simpa [truncate] using hPrevFalse
      have hinner : weight (truncate (truncate w)) = Nat.fib (m + 2) - 1 := by
        rw [weight_of_lastTrue hLastTrue, hmid, fib_endpoint_step] at hw
        exact Nat.add_right_cancel hw
      have hrec := endpointWord_unique (truncate (truncate w))
        (no11_truncate (no11_truncate hwNo11)) hinner
      have htrunc_eq : truncate w = snoc (endpointWord m) false := by
        calc
          truncate w = snoc (truncate (truncate w)) ((truncate w) ⟨m, by omega⟩) := by
            simpa using (X.snoc_truncate_last (truncate w)).symm
          _ = snoc (truncate (truncate w)) false := by
            simpa [truncate] using congrArg (snoc (truncate (truncate w))) (show (truncate w) ⟨m, by omega⟩ = false by simpa [truncate] using hPrevFalse)
          _ = snoc (endpointWord m) false := by rw [hrec]
      calc
        w = snoc (truncate w) true := by
          simpa [hLastTrue] using (X.snoc_truncate_last w).symm
        _ = snoc (snoc (endpointWord m) false) true := by rw [htrunc_eq]
        _ = endpointWord (m + 2) := by simp [endpointWord]

/-- Paper-facing seeds package for endpoint `M_m - 1 = F_{m+2} - 1`. -/
theorem paper_fold_endpoint_Mm_minus_one_unique_seeds (m : ℕ) :
    No11 (endpointWord m) ∧
    weight (endpointWord m) = Nat.fib (m + 2) - 1 ∧
    ∀ w : Word m, No11 w → weight w = Nat.fib (m + 2) - 1 → w = endpointWord m := by
  exact ⟨endpointWord_no11 m, endpointWord_weight m, fun w hwNo11 hw => endpointWord_unique w hwNo11 hw⟩

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_fold_endpoint_Mm_minus_one_unique_package (m : ℕ) :
    No11 (endpointWord m) ∧
    weight (endpointWord m) = Nat.fib (m + 2) - 1 ∧
    ∀ w : Word m, No11 w → weight w = Nat.fib (m + 2) - 1 → w = endpointWord m :=
  paper_fold_endpoint_Mm_minus_one_unique_seeds m

end Omega.Folding.EndpointMmMinusOneUnique
