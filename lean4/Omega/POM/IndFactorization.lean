import Mathlib.Tactic
import Omega.POM.IndependenceDpRadius2

namespace Omega.POM

private lemma dropConflictsRadius2_eq_self_of_separated (t : Nat) :
    ∀ xs : List Nat, (∀ j, j ∈ xs → t + 2 < j) → dropConflictsRadius2 t xs = xs
  | [], _ => by
      simp [dropConflictsRadius2]
  | j :: js, hsep => by
      have hj : t + 2 < j := hsep j (by simp)
      have hjs : ∀ k, k ∈ js → t + 2 < k := by
        intro k hk
        exact hsep k (by simp [hk])
      have hnot : ¬ j ≤ t + 2 := Nat.not_le_of_gt hj
      simpa [dropConflictsRadius2, hnot] using
        congrArg (List.cons j) (dropConflictsRadius2_eq_self_of_separated t js hjs)

private lemma dropConflictsRadius2_append_right (t : Nat) :
    ∀ xs ys : List Nat, (∀ j, j ∈ ys → t + 2 < j) →
      dropConflictsRadius2 t (xs ++ ys) = dropConflictsRadius2 t xs ++ ys
  | [], ys, hsep => by
      simpa using dropConflictsRadius2_eq_self_of_separated t ys hsep
  | i :: is, ys, hsep => by
      by_cases hi : i ≤ t + 2
      · simpa [dropConflictsRadius2, hi] using dropConflictsRadius2_append_right t is ys hsep
      · simpa [dropConflictsRadius2, hi] using
          congrArg (List.cons i) (dropConflictsRadius2_append_right t is ys hsep)

private lemma mem_of_mem_dropConflictsRadius2 {t i : Nat} {xs : List Nat} :
    i ∈ dropConflictsRadius2 t xs → i ∈ xs := by
  intro h
  induction xs with
  | nil =>
      simp [dropConflictsRadius2] at h
  | cons j js ih =>
      by_cases hj : j ≤ t + 2
      · simp [dropConflictsRadius2, hj] at h
        exact List.mem_cons_of_mem _ (ih h)
      · simp [dropConflictsRadius2, hj] at h
        simpa [List.mem_cons] using h

private theorem indepCountRadius2_append_factor
    (left right : List Nat)
    (hsep : ∀ i, i ∈ left → ∀ j, j ∈ right → i + 2 < j) :
    indepCountRadius2 (left ++ right) = indepCountRadius2 left * indepCountRadius2 right := by
  have hrec :
      ∀ n : Nat, ∀ left : List Nat, left.length = n → ∀ right : List Nat,
        (∀ i, i ∈ left → ∀ j, j ∈ right → i + 2 < j) →
          indepCountRadius2 (left ++ right) = indepCountRadius2 left * indepCountRadius2 right := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro left hlen right hsep
        cases left with
        | nil =>
            simp [indepCountRadius2] at hlen ⊢
        | cons t ts =>
            have hlen_eq : ts.length + 1 = n := by
              simpa using hlen
            have hlen_ts : ts.length < n := by
              omega
            have hlen_drop : (dropConflictsRadius2 t ts).length < n := by
              exact lt_of_le_of_lt (dropConflictsRadius2_length_le t ts) hlen_ts
            have hsep_ts : ∀ i, i ∈ ts → ∀ j, j ∈ right → i + 2 < j := by
              intro i hi j hj
              exact hsep i (by simp [hi]) j hj
            have hsep_drop : ∀ i, i ∈ dropConflictsRadius2 t ts → ∀ j, j ∈ right → i + 2 < j := by
              intro i hi j hj
              exact hsep i (by simp [mem_of_mem_dropConflictsRadius2 hi]) j hj
            calc
              indepCountRadius2 ((t :: ts) ++ right)
                  = indepCountRadius2 (ts ++ right) +
                      indepCountRadius2 (dropConflictsRadius2 t (ts ++ right)) := by
                        simp [indepCountRadius2]
              _ = indepCountRadius2 (ts ++ right) + indepCountRadius2 (dropConflictsRadius2 t ts ++ right) := by
                    rw [dropConflictsRadius2_append_right]
                    intro j hj
                    exact hsep t (by simp) j hj
              _ = indepCountRadius2 ts * indepCountRadius2 right +
                    indepCountRadius2 (dropConflictsRadius2 t ts ++ right) := by
                    rw [ih ts.length hlen_ts ts rfl right hsep_ts]
              _ = indepCountRadius2 ts * indepCountRadius2 right +
                    indepCountRadius2 (dropConflictsRadius2 t ts) * indepCountRadius2 right := by
                    rw [ih (dropConflictsRadius2 t ts).length hlen_drop (dropConflictsRadius2 t ts) rfl right
                      hsep_drop]
              _ = (indepCountRadius2 ts + indepCountRadius2 (dropConflictsRadius2 t ts)) *
                    indepCountRadius2 right := by
                    rw [Nat.add_mul]
              _ = indepCountRadius2 (t :: ts) * indepCountRadius2 right := by
                    simp [indepCountRadius2]
  exact hrec left.length left rfl right hsep

/-- Paper label: `prop:pom-ind-factorization`. -/
theorem paper_pom_ind_factorization
    (left right : List Nat) (hleft : left.Pairwise (fun a b => a < b))
    (hright : right.Pairwise (fun a b => a < b))
    (hsep : ∀ i, i ∈ left → ∀ j, j ∈ right → i + 2 < j) :
    indepCountRadius2 (left ++ right) = indepCountRadius2 left * indepCountRadius2 right := by
  let _ := hleft
  let _ := hright
  simpa using indepCountRadius2_append_factor left right hsep

end Omega.POM
