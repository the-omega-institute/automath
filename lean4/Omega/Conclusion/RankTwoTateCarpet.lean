import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-prefix data for the rank-two `B`-adic digit carpet. -/
structure conclusion_rank_two_tate_carpet_data where
  B : ℕ
  M : ℕ
  hB : 2 ≤ B
  hM : M < B

namespace conclusion_rank_two_tate_carpet_data

abbrev conclusion_rank_two_tate_carpet_digit (D : conclusion_rank_two_tate_carpet_data) :=
  Fin (D.M + 1)

abbrev conclusion_rank_two_tate_carpet_digitPair
    (D : conclusion_rank_two_tate_carpet_data) :=
  D.conclusion_rank_two_tate_carpet_digit × D.conclusion_rank_two_tate_carpet_digit

def conclusion_rank_two_tate_carpet_pairValue (D : conclusion_rank_two_tate_carpet_data) :
    List D.conclusion_rank_two_tate_carpet_digitPair → ℕ × ℕ
  | [] => (0, 0)
  | p :: ps =>
      (p.1.val + D.B * (D.conclusion_rank_two_tate_carpet_pairValue ps).1,
        p.2.val + D.B * (D.conclusion_rank_two_tate_carpet_pairValue ps).2)

def conclusion_rank_two_tate_carpet_cylinderCount
    (D : conclusion_rank_two_tate_carpet_data) (n : ℕ) : ℕ :=
  Fintype.card (Fin n → D.conclusion_rank_two_tate_carpet_digitPair)

def uniqueDigitExpansion (D : conclusion_rank_two_tate_carpet_data) : Prop :=
  ∀ w z : List D.conclusion_rank_two_tate_carpet_digitPair,
    w.length = z.length →
      D.conclusion_rank_two_tate_carpet_pairValue w =
        D.conclusion_rank_two_tate_carpet_pairValue z →
        w = z

def selfSimilarDisjointUnion (D : conclusion_rank_two_tate_carpet_data) : Prop :=
  ∀ n : ℕ,
    D.conclusion_rank_two_tate_carpet_cylinderCount (n + 1) =
      Fintype.card D.conclusion_rank_two_tate_carpet_digitPair *
        D.conclusion_rank_two_tate_carpet_cylinderCount n

def dimensionFormula (D : conclusion_rank_two_tate_carpet_data) : Prop :=
  ∀ n : ℕ,
    D.conclusion_rank_two_tate_carpet_cylinderCount n = (D.M + 1) ^ (2 * n)

def fullAtMax (D : conclusion_rank_two_tate_carpet_data) : Prop :=
  D.M = D.B - 1 → Fintype.card D.conclusion_rank_two_tate_carpet_digitPair = D.B ^ 2

def nullInteriorProper (D : conclusion_rank_two_tate_carpet_data) : Prop :=
  D.M ≤ D.B - 2 → D.M + 1 < D.B

lemma conclusion_rank_two_tate_carpet_digit_lt_base
    (D : conclusion_rank_two_tate_carpet_data)
    (a : D.conclusion_rank_two_tate_carpet_digit) : a.val < D.B := by
  have hle : D.M + 1 ≤ D.B := Nat.succ_le_of_lt D.hM
  exact lt_of_lt_of_le a.isLt hle

lemma conclusion_rank_two_tate_carpet_pairValue_injective
    (D : conclusion_rank_two_tate_carpet_data) :
    D.uniqueDigitExpansion := by
  intro w
  induction w with
  | nil =>
      intro z hlen hval
      cases z with
      | nil => rfl
      | cons z zs => simp at hlen
  | cons p ps ih =>
      intro z hlen hval
      cases z with
      | nil => simp at hlen
      | cons q qs =>
          have hlen_tail : ps.length = qs.length := by
            simpa using hlen
          have hfirst :
              p.1.val + D.B * (D.conclusion_rank_two_tate_carpet_pairValue ps).1 =
                q.1.val + D.B * (D.conclusion_rank_two_tate_carpet_pairValue qs).1 := by
            exact congrArg Prod.fst hval
          have hsecond :
              p.2.val + D.B * (D.conclusion_rank_two_tate_carpet_pairValue ps).2 =
                q.2.val + D.B * (D.conclusion_rank_two_tate_carpet_pairValue qs).2 := by
            exact congrArg Prod.snd hval
          have hhead_fst : p.1 = q.1 := by
            apply Fin.ext
            have hmod := congrArg (fun x : ℕ => x % D.B) hfirst
            have hp := D.conclusion_rank_two_tate_carpet_digit_lt_base p.1
            have hq := D.conclusion_rank_two_tate_carpet_digit_lt_base q.1
            simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq]
              using hmod
          have hhead_snd : p.2 = q.2 := by
            apply Fin.ext
            have hmod := congrArg (fun x : ℕ => x % D.B) hsecond
            have hp := D.conclusion_rank_two_tate_carpet_digit_lt_base p.2
            have hq := D.conclusion_rank_two_tate_carpet_digit_lt_base q.2
            simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq]
              using hmod
          have hhead : p = q := by
            cases p
            cases q
            simp_all
          have htail_value :
              D.conclusion_rank_two_tate_carpet_pairValue ps =
                D.conclusion_rank_two_tate_carpet_pairValue qs := by
            rw [hhead] at hfirst hsecond
            have hBpos : 0 < D.B := lt_of_lt_of_le (by norm_num : 0 < 2) D.hB
            have htail_fst :
                (D.conclusion_rank_two_tate_carpet_pairValue ps).1 =
                  (D.conclusion_rank_two_tate_carpet_pairValue qs).1 := by
              have hmul :
                  D.B * (D.conclusion_rank_two_tate_carpet_pairValue ps).1 =
                    D.B * (D.conclusion_rank_two_tate_carpet_pairValue qs).1 := by
                exact Nat.add_left_cancel hfirst
              exact Nat.eq_of_mul_eq_mul_left hBpos hmul
            have htail_snd :
                (D.conclusion_rank_two_tate_carpet_pairValue ps).2 =
                  (D.conclusion_rank_two_tate_carpet_pairValue qs).2 := by
              have hmul :
                  D.B * (D.conclusion_rank_two_tate_carpet_pairValue ps).2 =
                    D.B * (D.conclusion_rank_two_tate_carpet_pairValue qs).2 := by
                exact Nat.add_left_cancel hsecond
              exact Nat.eq_of_mul_eq_mul_left hBpos hmul
            exact Prod.ext htail_fst htail_snd
          have htail := ih qs hlen_tail htail_value
          simp [hhead, htail]

lemma conclusion_rank_two_tate_carpet_self_similar_disjoint_union
    (D : conclusion_rank_two_tate_carpet_data) : D.selfSimilarDisjointUnion := by
  intro n
  simp [conclusion_rank_two_tate_carpet_cylinderCount, Nat.pow_succ, Nat.mul_comm]

lemma conclusion_rank_two_tate_carpet_dimension_formula
    (D : conclusion_rank_two_tate_carpet_data) : D.dimensionFormula := by
  intro n
  rw [conclusion_rank_two_tate_carpet_cylinderCount]
  rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  calc
    ((D.M + 1) * (D.M + 1)) ^ n = ((D.M + 1) ^ 2) ^ n := by
      congr 1
      ring
    _ = (D.M + 1) ^ (2 * n) := by
      rw [pow_mul]

lemma conclusion_rank_two_tate_carpet_full_at_max
    (D : conclusion_rank_two_tate_carpet_data) : D.fullAtMax := by
  intro hM
  have hBpos : 0 < D.B := lt_of_lt_of_le (by norm_num : 0 < 2) D.hB
  have hcard : D.M + 1 = D.B := by omega
  simp [hcard, Nat.pow_two]

lemma conclusion_rank_two_tate_carpet_null_interior_proper
    (D : conclusion_rank_two_tate_carpet_data) : D.nullInteriorProper := by
  intro hproper
  have hB : 2 ≤ D.B := D.hB
  omega

end conclusion_rank_two_tate_carpet_data

open conclusion_rank_two_tate_carpet_data

/-- Paper label: `thm:conclusion-rank-two-tate-carpet`. -/
theorem paper_conclusion_rank_two_tate_carpet
    (D : conclusion_rank_two_tate_carpet_data) :
    D.uniqueDigitExpansion ∧ D.selfSimilarDisjointUnion ∧ D.dimensionFormula ∧
      D.fullAtMax ∧ D.nullInteriorProper := by
  exact
    ⟨D.conclusion_rank_two_tate_carpet_pairValue_injective,
      D.conclusion_rank_two_tate_carpet_self_similar_disjoint_union,
      D.conclusion_rank_two_tate_carpet_dimension_formula,
      D.conclusion_rank_two_tate_carpet_full_at_max,
      D.conclusion_rank_two_tate_carpet_null_interior_proper⟩

end Omega.Conclusion
