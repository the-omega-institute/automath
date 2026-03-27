import Omega.Combinatorics.PathIndSet
import Omega.Folding.Weight
import Omega.Folding.Fold
import Omega.Folding.MaxFiber
import Omega.Folding.MomentRecurrence

namespace Omega

-- ══════════════════════════════════════════════════════════════
-- wordSupport: X_m → independent sets
-- ══════════════════════════════════════════════════════════════

/-- The support of a word: {i : Fin m | w i = true}. -/
def wordSupport (w : Word m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => w i = true)

/-- No11 word's support is path-independent.
    thm:pom-wordSupport-pathInd -/
theorem wordSupport_isPathIndependent {w : Word m} (hw : No11 w) :
    IsPathIndependent m (wordSupport w) := by
  intro i hi j hj hadj
  simp only [wordSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  -- i.val + 1 = j.val, w i = true, w j = true → contradicts No11
  have hiLt : i.val < m := i.isLt
  have hjLt : j.val < m := j.isLt
  have hget_i : get w i.val = true := by rw [get]; simp [hiLt, hi]
  have hget_j : get w (i.val + 1) = true := by
    rw [get]; rw [hadj]; simp [hjLt, hj]
  exact hw i.val hget_i hget_j

-- ══════════════════════════════════════════════════════════════
-- indSetToWord: independent sets → Word m
-- ══════════════════════════════════════════════════════════════

/-- Characteristic function of an independent set as a word. -/
def indSetToWord (S : Finset (Fin m)) : Word m :=
  fun i => if i ∈ S then true else false

/-- Independent set's word satisfies No11.
    thm:pom-indSetToWord-no11 -/
theorem indSetToWord_no11 {S : Finset (Fin m)} (hS : IsPathIndependent m S) :
    No11 (indSetToWord S) := by
  intro i hi hi1
  -- Extract i < m from get(indSetToWord S, i) = true
  unfold get indSetToWord at hi hi1
  split at hi
  · rename_i hiLt
    split at hi1
    · rename_i hi1Lt
      -- hi : (if ⟨i,_⟩ ∈ S then true else false) = true
      -- hi1 : (if ⟨i+1,_⟩ ∈ S then true else false) = true
      have h1 : (⟨i, hiLt⟩ : Fin m) ∈ S := by split at hi <;> simp_all
      have h2 : (⟨i + 1, hi1Lt⟩ : Fin m) ∈ S := by split at hi1 <;> simp_all
      exact hS ⟨i, hiLt⟩ h1 ⟨i + 1, hi1Lt⟩ h2 rfl
    · exact absurd hi1 Bool.false_ne_true
  · exact absurd hi Bool.false_ne_true

-- ══════════════════════════════════════════════════════════════
-- Mutual inverses
-- ══════════════════════════════════════════════════════════════

/-- wordSupport ∘ indSetToWord = id.
    thm:pom-wordSupport-indSetToWord -/
theorem wordSupport_indSetToWord (S : Finset (Fin m)) :
    wordSupport (indSetToWord S) = S := by
  ext i
  simp only [wordSupport, indSetToWord, Finset.mem_filter, Finset.mem_univ, true_and]
  split <;> simp_all

/-- indSetToWord ∘ wordSupport = id.
    thm:pom-indSetToWord-wordSupport -/
theorem indSetToWord_wordSupport (w : Word m) :
    indSetToWord (wordSupport w) = w := by
  funext i
  simp only [indSetToWord, wordSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  cases w i <;> simp

-- ══════════════════════════════════════════════════════════════
-- Equivalence X_m ≃ PathIndSets
-- ══════════════════════════════════════════════════════════════

/-- The type of path-independent sets on Fin m. -/
def PathIndSets (m : Nat) := { S : Finset (Fin m) // IsPathIndependent m S }

/-- X_m ≃ independent sets on P_m.
    thm:pom-xEquivPathIndSet -/
noncomputable def xEquivPathIndSet (m : Nat) : X m ≃ PathIndSets m where
  toFun x := ⟨wordSupport x.1, wordSupport_isPathIndependent x.2⟩
  invFun S := ⟨indSetToWord S.1, indSetToWord_no11 S.2⟩
  left_inv x := Subtype.ext (indSetToWord_wordSupport x.1)
  right_inv S := Subtype.ext (wordSupport_indSetToWord S.1)



-- ══════════════════════════════════════════════════════════════
-- popcount
-- ══════════════════════════════════════════════════════════════

/-- Number of true bits in a word. -/
def popcount (w : Word m) : Nat := (wordSupport w).card

theorem popcount_eq_count_true (w : Word m) :
    popcount w = (Finset.univ.filter (fun i : Fin m => w i = true)).card := rfl

/-- thm:pom-popcount-allFalse -/
theorem popcount_allFalse : popcount (fun (_ : Fin m) => false) = 0 := by
  simp [popcount, wordSupport]

/-- thm:pom-popcount-allTrue -/
theorem popcount_allTrue : popcount (fun (_ : Fin m) => true) = m := by
  simp [popcount, wordSupport]

-- ══════════════════════════════════════════════════════════════
-- popcount complement + statistics
-- ══════════════════════════════════════════════════════════════

/-- popcount(bitwise complement) + popcount = m.
    thm:pom-popcount-not -/
theorem popcount_not (w : Word m) :
    popcount (fun i => !w i) + popcount w = m := by
  simp only [popcount, wordSupport]
  have hsplit : (Finset.univ : Finset (Fin m)) =
      Finset.univ.filter (fun i => (!w i) = true) ∪
      Finset.univ.filter (fun i => w i = true) := by
    ext i; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and]
    cases w i <;> simp
  have hdisj : Disjoint (Finset.univ.filter (fun i : Fin m => (!w i) = true))
      (Finset.univ.filter (fun i : Fin m => w i = true)) := by
    apply Finset.disjoint_filter.mpr; intro i _ h1 h2
    cases hb : w i <;> simp [hb] at h1 h2
  calc (Finset.univ.filter (fun i : Fin m => (!w i) = true)).card +
      (Finset.univ.filter (fun i : Fin m => w i = true)).card
      = (Finset.univ.filter (fun i => (!w i) = true) ∪
        Finset.univ.filter (fun i => w i = true)).card :=
          (Finset.card_union_of_disjoint hdisj).symm
    _ = Finset.univ.card := by rw [← hsplit]
    _ = Fintype.card (Fin m) := by rw [Finset.card_univ]
    _ = m := Fintype.card_fin m

/-- popcount = 0 iff word is all-false.
    thm:pom-popcount-eq-zero-iff -/
theorem popcount_eq_zero_iff (x : X m) :
    popcount x.1 = 0 ↔ x = ⟨fun _ => false, no11_allFalse⟩ := by
  constructor
  · intro h
    have hempty : wordSupport x.1 = ∅ := Finset.card_eq_zero.mp h
    apply Subtype.ext; funext i
    have : i ∉ wordSupport x.1 := by rw [hempty]; simp
    simp [wordSupport, Finset.mem_filter] at this; exact this
  · intro h; rw [h]; exact popcount_allFalse

/-- popcount(truncate w) ≤ popcount(w).
    thm:pom-popcount-truncate-le -/
theorem popcount_truncate_le (w : Word (m + 1)) : popcount (truncate w) ≤ popcount w := by
  simp only [popcount, wordSupport]
  -- Inject Fin m → Fin (m+1) via Fin.castSucc
  apply Finset.card_le_card_of_injOn Fin.castSucc
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simp [truncate] at hi; exact hi
  · intro i _ j _ h; exact Fin.castSucc_injective _ h

/-- Total popcount across X_m. -/
noncomputable def totalPopcount (m : Nat) : Nat := ∑ x : X m, popcount x.1

/-- thm:pom-totalPopcount-zero -/
theorem totalPopcount_zero : totalPopcount 0 = 0 := by
  simp [totalPopcount, popcount, wordSupport]

-- totalPopcount_one deferred (noncomputable + decide incompatible)

-- ══════════════════════════════════════════════════════════════
-- Weight surjectivity
-- ══════════════════════════════════════════════════════════════

/-- Every weight value in [0, F_{m+3}-2] is achieved by some word.
    thm:pom-weight-surjective -/
theorem weight_surjective (m n : Nat) (hn : n ≤ Nat.fib (m + 3) - 2) :
    ∃ w : Word m, weight w = n := by
  induction m generalizing n with
  | zero =>
    have : n = 0 := by simp [Nat.fib] at hn; omega
    exact ⟨fun i => False.elim (Nat.not_lt_zero _ i.isLt), by simp [weight]; omega⟩
  | succ m ih =>
    by_cases hlt : n ≤ Nat.fib (m + 3) - 2
    · obtain ⟨v, hv⟩ := ih n hlt
      exact ⟨snoc v false, by simp [weight, weight_snoc, hv]⟩
    · push_neg at hlt
      have hfib4 := Nat.fib_add_two (n := m + 2)
      rw [show m + 2 + 2 = m + 4 from rfl, show m + 2 + 1 = m + 3 from rfl] at hfib4
      have hge : Nat.fib (m + 2) ≤ n := by
        have hfib3 := Nat.fib_add_two (n := m + 1)
        rw [show m + 1 + 2 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl] at hfib3
        have := fib_succ_pos m
        omega
      have hle : n - Nat.fib (m + 2) ≤ Nat.fib (m + 3) - 2 := by
        have : Nat.fib (m + 1 + 3) = Nat.fib (m + 4) := rfl; omega
      obtain ⟨v, hv⟩ := ih (n - Nat.fib (m + 2)) hle
      exact ⟨snoc v true, by simp [weight, weight_snoc, hv]; omega⟩

/-- ewc(m, n) > 0 for n ≤ F_{m+3}-2.
    thm:pom-ewc-pos-of-le -/
theorem ewc_pos_of_le (m n : Nat) (hn : n ≤ Nat.fib (m + 3) - 2) :
    0 < exactWeightCount m n := by
  obtain ⟨w, hw⟩ := weight_surjective m n hn
  exact Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩

/-- d(x) ≥ 2 when sv(x) + F ≤ max weight.
    thm:pom-fiberMultiplicity-ge-two-of-sv-le -/
theorem fiberMultiplicity_ge_two_of_sv_le (x : X m)
    (h : stableValue x + Nat.fib (m + 2) ≤ Nat.fib (m + 3) - 2) :
    2 ≤ X.fiberMultiplicity x := by
  rw [fiberMultiplicity_eq_two_ewc]
  have h1 := ewc_stableValue_pos x
  have h2 := ewc_pos_of_le m _ h; omega

-- ══════════════════════════════════════════════════════════════
-- Weight decomposition + fiber wrappers
-- ══════════════════════════════════════════════════════════════

/-- thm:pom-weight-truncate-add -/
theorem weight_truncate_add (w : Word (m + 1)) :
    weight w = weight (truncate w) +
    if w ⟨m, Nat.lt_succ_self m⟩ = true then Nat.fib (m + 2) else 0 := rfl

/-- thm:pom-weight-pos-iff -/
theorem weight_pos_iff (w : Word m) :
    0 < weight w ↔ ∃ i : Fin m, w i = true := by
  constructor
  · intro hpos; by_contra h; push_neg at h
    have hall : w = fun _ => false := funext (fun i => by
      have := h i; simp only [ne_eq, Bool.not_eq_true] at this; exact this)
    rw [hall, weight_allFalse] at hpos; omega
  · intro ⟨i, hi⟩
    -- weight ≥ F_{i+2} ≥ 1
    calc 0 < 1 := by omega
      _ ≤ Nat.fib (i.val + 2) := fib_succ_pos (i.val + 1)
      _ ≤ weight w := by
        -- The contribution of bit i is F_{i+2}, which is ≤ weight
        induction m with
        | zero => exact absurd i.isLt (Nat.not_lt_zero _)
        | succ n ih =>
          rw [weight_truncate_add]
          by_cases hlt : i.val < n
          · have : Nat.fib (i.val + 2) ≤ weight (truncate w) :=
              ih (truncate w) ⟨i.val, hlt⟩ (by simp [truncate]; exact hi)
            omega
          · have : i.val = n := Nat.eq_of_lt_succ_of_not_lt i.isLt hlt
            rw [this]; simp [show w ⟨n, Nat.lt_succ_self n⟩ = true from by
              have : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext this
              rw [← this]; exact hi]

/-- thm:pom-Fold-of-stable -/
theorem Fold_of_stable' (x : X m) : Fold x.1 = x := Fold_stable x

/-- thm:pom-fiber-self-mem -/
theorem fiber_self_mem (x : X m) : x.1 ∈ X.fiber x := X.self_mem_fiber x

-- fiberMultiplicity_eq_one_of_sv_ge deferred (ewc uniqueness proof complex)

-- ══════════════════════════════════════════════════════════════
-- D(m) bounds
-- ══════════════════════════════════════════════════════════════

/-- D(m) ≤ F(m+2).
    thm:pom-maxFiberMultiplicity-le-fib -/
theorem maxFiberMultiplicity_le_fib (m : Nat) :
    X.maxFiberMultiplicity m ≤ Nat.fib (m + 2) := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => rw [X.maxFiberMultiplicity_zero]; exact one_le_fib_succ 1
    | 1 => rw [X.maxFiberMultiplicity_one]; exact one_le_fib_succ 2
    | m + 2 =>
      have h1 := ih (m + 1) (by omega)
      have h2 := ih m (by omega)
      have hle := X.maxFiberMultiplicity_le_add m
      have hfib := fib_succ_succ' (m + 2)
      rw [show m + 2 + 2 = m + 4 from rfl, show m + 2 + 1 = m + 3 from rfl] at hfib
      linarith

/-- d(x) ≤ F(m+2) for all x.
    thm:pom-fiberMultiplicity-le-fib -/
theorem fiberMultiplicity_le_fib (x : X m) :
    X.fiberMultiplicity x ≤ Nat.fib (m + 2) :=
  (X.fiberMultiplicity_le_max x).trans (maxFiberMultiplicity_le_fib m)

/-- D(m)² ≤ S_2(m).
    thm:pom-maxFiberMultiplicity-sq-le-momentSum -/
theorem maxFiberMultiplicity_sq_le_momentSum (m : Nat) :
    X.maxFiberMultiplicity m ^ 2 ≤ momentSum 2 m := by
  obtain ⟨x, hx⟩ := X.maxFiberMultiplicity_achieved m
  calc X.maxFiberMultiplicity m ^ 2 = X.fiberMultiplicity x ^ 2 := by rw [hx]
    _ ≤ ∑ y : X m, X.fiberMultiplicity y ^ 2 :=
        Finset.single_le_sum (f := fun y => X.fiberMultiplicity y ^ 2)
          (fun y _ => Nat.zero_le _) (Finset.mem_univ x)
    _ = momentSum 2 m := rfl

-- ══════════════════════════════════════════════════════════════
-- D(m) lower bounds + unboundedness
-- ══════════════════════════════════════════════════════════════

/-- D(m) ≥ ⌊m/2⌋ + 1.
    thm:pom-maxFiberMultiplicity-ge-half -/
theorem maxFiberMultiplicity_ge_half (m : Nat) :
    m / 2 + 1 ≤ X.maxFiberMultiplicity m := by
  calc m / 2 + 1
      = X.fiberMultiplicity (⟨fun _ => false, no11_allFalse⟩ : X m) :=
        (fiberMultiplicity_allFalse_closed m).symm
    _ ≤ X.maxFiberMultiplicity m := X.fiberMultiplicity_le_max _

/-- D(m) ≥ 2 for m ≥ 2.
    thm:pom-maxFiberMultiplicity-ge-two -/
theorem maxFiberMultiplicity_ge_two (m : Nat) (hm : 2 ≤ m) :
    2 ≤ X.maxFiberMultiplicity m := by
  have := maxFiberMultiplicity_ge_half m; omega

/-- D(m) is sandwiched: ⌊m/2⌋+1 ≤ D(m) ≤ F(m+2).
    thm:pom-maxFiberMultiplicity-bounds -/
theorem maxFiberMultiplicity_bounds (m : Nat) :
    m / 2 + 1 ≤ X.maxFiberMultiplicity m ∧
    X.maxFiberMultiplicity m ≤ Nat.fib (m + 2) :=
  ⟨maxFiberMultiplicity_ge_half m, maxFiberMultiplicity_le_fib m⟩

/-- D(m) is unbounded.
    thm:pom-maxFiberMultiplicity-unbounded -/
theorem maxFiberMultiplicity_unbounded : ∀ C, ∃ m, C < X.maxFiberMultiplicity m := by
  intro C; exact ⟨2 * C, by have := maxFiberMultiplicity_ge_half (2 * C); omega⟩

/-- S_2(m) ≥ D(m)² (named alias).
    thm:pom-momentSum-two-ge-maxFiber-sq -/
theorem momentSum_two_ge_maxFiber_sq (m : Nat) :
    X.maxFiberMultiplicity m ^ 2 ≤ momentSum 2 m :=
  maxFiberMultiplicity_sq_le_momentSum m

/-- weight(w) = Σ_{i ∈ wordSupport(w)} Nat.fib(i.val + 2). -/
theorem weight_eq_fib_sum (w : Word m) :
    weight w = ∑ i ∈ wordSupport w, Nat.fib (i.val + 2) := by
  rw [weight_eq_fib_ite_sum]
  -- ∑_{i : Fin m} (if w i then fib(i+2) else 0) = ∑_{i ∈ support} fib(i+2)
  rw [← Finset.sum_filter]
  rfl

-- ══════════════════════════════════════════════════════════════
-- Phase 117: popcount bound + PathIndSets card + appendFalse injective
-- ══════════════════════════════════════════════════════════════

/-- PathIndSets is finite (via equivalence with X m).
    prop:folding-stable-syntax-fibonacci-count -/
noncomputable instance instFintypePathIndSets (m : Nat) : Fintype (PathIndSets m) :=
  Fintype.ofEquiv (X m) (xEquivPathIndSet m)

/-- |PathIndSets m| = F_{m+2}.
    prop:folding-stable-syntax-fibonacci-count -/
theorem card_pathIndSets (m : Nat) :
    Fintype.card (PathIndSets m) = Nat.fib (m + 2) := by
  rw [← X.card_eq_fib m]
  exact Fintype.card_congr (xEquivPathIndSet m).symm

/-- X.appendFalse is injective.
    prop:folding-stable-syntax-terminal-recursion -/
theorem appendFalse_injective (m : Nat) : Function.Injective (X.appendFalse (m := m)) :=
  fun x y h => by
    have := congr_arg X.restrict h
    rwa [X.restrict_appendFalse, X.restrict_appendFalse] at this

/-- No11 words have at most ⌈m/2⌉ true bits.
    thm:pom-fiber-indset-factorization -/
theorem popcount_le_half (x : X m) : (wordSupport x.1).card ≤ (m + 1) / 2 := by
  -- Proof by strong induction on m.
  -- Key: No11 means no two adjacent bits are true.
  -- For m+2: at most one of the last two bits is true.
  -- If last bit false: popcount = popcount(truncate x) ≤ ((m+1)+1)/2 = (m+2)/2
  --   and (m+2)/2 ≤ (m+3)/2 = ((m+2)+1)/2. ✓
  -- If last bit true: second-to-last must be false (No11).
  --   popcount = popcount(truncate(truncate x)) + 1 ≤ (m+1)/2 + 1
  --   and (m+1)/2 + 1 = (m+3)/2 when m odd, = (m+2)/2 ≤ (m+3)/2 when m even. ✓
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => simp [wordSupport]
    | 1 =>
      calc (wordSupport x.1).card
          ≤ (Finset.univ : Finset (Fin 1)).card := Finset.card_filter_le _ _
        _ = 1 := by simp
    | m + 2 =>
      -- Use popcount_truncate_le: (wordSupport (truncate w)).card ≤ (wordSupport w).card
      -- Strategy: bound popcount by IH at m+1 (last bit false) or m (last bit true)
      by_cases hLast : x.1 ⟨m + 1, by omega⟩ = true
      · -- Last bit true → second-to-last false by No11
        have hPrev : x.1 ⟨m, by omega⟩ = false := by
          by_contra hc; push_neg at hc
          have ht : x.1 ⟨m, by omega⟩ = true := by cases hb : x.1 ⟨m, by omega⟩ <;> simp_all
          have hg1 : get x.1 m = true := by rw [get]; simp [show m < m + 2 from by omega]; exact ht
          have hg2 : get x.1 (m + 1) = true := by rw [get]; simp [show m + 1 < m + 2 from by omega]; exact hLast
          exact x.2 m hg1 hg2
        -- Every true bit at position < m is also a true bit of truncate(truncate x)
        -- Plus the one true bit at position m+1
        -- So wordSupport x ⊆ (image of wordSupport(trunc²x)) ∪ {m+1}
        -- Card ≤ card(trunc²x support) + 1 ≤ (m+1)/2 + 1
        have htrunc2 := ih m (by omega) ⟨truncate (truncate x.1), no11_truncate (no11_truncate x.2)⟩
        -- Need: card ≤ card_trunc + 1 ≤ (m+1)/2 + 1 = (m+3)/2
        suffices hsuff : (wordSupport x.1).card ≤
            (wordSupport (truncate (truncate x.1))).card + 1 by
          calc (wordSupport x.1).card ≤ _ + 1 := hsuff
            _ ≤ (m + 1) / 2 + 1 := Nat.add_le_add_right htrunc2 1
            _ = (m + 2 + 1) / 2 := by omega
        -- wordSupport x ⊆ (Fin.castSucc ∘ Fin.castSucc '' wordSupport(trunc²x)) ∪ {⟨m+1,_⟩}
        calc (wordSupport x.1).card
            ≤ ((wordSupport (truncate (truncate x.1))).image
                (fun i : Fin m => (⟨i.val, by omega⟩ : Fin (m + 2))) ∪
               {⟨m + 1, by omega⟩}).card := by
              apply Finset.card_le_card; intro ⟨i, hi⟩ hmem
              simp only [wordSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
              simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, Fin.ext_iff,
                wordSupport, Finset.mem_filter, Finset.mem_univ, true_and]
              by_cases him : i < m
              · left; exact ⟨⟨i, him⟩, by simp [truncate]; exact hmem, rfl⟩
              · right
                have : i = m ∨ i = m + 1 := by omega
                rcases this with rfl | rfl
                · -- Position m is false
                  exact absurd hmem (by simp [hPrev])
                · rfl
          _ ≤ (wordSupport (truncate (truncate x.1))).card + 1 := by
              calc _ ≤ ((wordSupport (truncate (truncate x.1))).image _).card +
                       ({⟨m + 1, by omega⟩} : Finset (Fin (m + 2))).card :=
                      Finset.card_union_le _ _
                _ ≤ (wordSupport (truncate (truncate x.1))).card + 1 := by
                      apply Nat.add_le_add_right
                      exact Finset.card_image_le
      · -- Last bit false: popcount ≤ popcount(truncate x)
        have hFalse : x.1 ⟨m + 1, by omega⟩ = false := by
          cases hb : x.1 ⟨m + 1, by omega⟩ <;> simp_all
        have htrunc := ih (m + 1) (by omega) ⟨truncate x.1, no11_truncate x.2⟩
        calc (wordSupport x.1).card
            ≤ (wordSupport (truncate x.1)).card := by
              -- All true bits of x have index < m+1 (since position m+1 is false)
              -- so wordSupport x injects into wordSupport(truncate x)
              have hmem_bound : ∀ i ∈ wordSupport x.1, i.val < m + 1 := by
                intro ⟨i, hi⟩ hmem
                simp only [wordSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
                by_contra hge; push_neg at hge
                have heq : i = m + 1 := Nat.le_antisymm (by omega) hge
                have : x.1 ⟨m + 1, by omega⟩ = true := by rwa [show (⟨i, hi⟩ : Fin (m+2)) = ⟨m+1, by omega⟩ from Fin.ext heq] at hmem
                rw [hFalse] at this; exact absurd this (by decide)
              -- Use Fin.castSucc embedding from Fin(m+1) to Fin(m+2) in reverse
              -- All elements of wordSupport x have index < m+1
              rw [show (wordSupport x.1) = (wordSupport (truncate x.1)).image Fin.castSucc from by
                ext ⟨i, hi⟩; simp only [wordSupport, Finset.mem_filter, Finset.mem_univ, true_and,
                  Finset.mem_image, Fin.castSucc]
                constructor
                · intro hmem
                  have hlt := hmem_bound ⟨i, hi⟩ (by simp [wordSupport, Finset.mem_filter]; exact hmem)
                  exact ⟨⟨i, hlt⟩, by simp [truncate]; exact hmem, Fin.ext rfl⟩
                · rintro ⟨⟨j, hj⟩, hmem, heq⟩
                  simp [Fin.ext_iff] at heq; subst heq
                  simp [truncate] at hmem; exact hmem]
              exact Finset.card_image_le
          _ ≤ ((m + 1) + 1) / 2 := htrunc
          _ ≤ ((m + 2) + 1) / 2 := by omega


/-- popcount(w) ≤ weight(w): each true bit contributes F(i+2) ≥ 1 to weight.
    bridge:popcount-weight -/
theorem popcount_le_weight (w : Word m) : popcount w ≤ weight w := by
  rw [weight_eq_fib_sum]
  simp only [popcount, wordSupport]
  -- Σ_{i ∈ support} F(i+2) ≥ Σ_{i ∈ support} 1 = |support| = popcount
  calc (Finset.univ.filter (fun i : Fin m => w i = true)).card
      = ∑ _ ∈ Finset.univ.filter (fun i : Fin m => w i = true), 1 := by simp
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin m => w i = true), Nat.fib (i.val + 2) := by
        apply Finset.sum_le_sum; intro i _; exact fib_succ_pos (i.val + 1)

/-- Paper label: X_m ≃ path-independent sets on P_m.
    def:pom-fibonacci-cube -/
theorem paper_fibonacci_cube_equiv (m : Nat) :
    Nonempty (X m ≃ PathIndSets m) := ⟨xEquivPathIndSet m⟩

/-- Paper: |X_m| = F_{m+2} and X_m ≃ PathIndSets.
    def:pom-fibonacci-cube -/
theorem paper_fibonacci_cube (m : Nat) :
    Fintype.card (X m) = Nat.fib (m + 2) ∧ Nonempty (X m ≃ PathIndSets m) :=
  ⟨X.card_eq_fib m, ⟨xEquivPathIndSet m⟩⟩

-- ══════════════════════════════════════════════════════════════
-- Phase 170
-- ══════════════════════════════════════════════════════════════

/-- D(m) < 2^m for all m ≥ 2. cor:pom-max-fiber-rate-endpoint. -/
theorem maxFiber_lt_wordcount (m : Nat) (hm : 2 ≤ m) :
    X.maxFiberMultiplicity m < 2 ^ m :=
  Nat.lt_of_le_of_lt (maxFiberMultiplicity_le_fib m) (fib_lt_pow_two_of_ge_two m hm)

-- ══════════════════════════════════════════════════════════════
-- Phase 173
-- ══════════════════════════════════════════════════════════════

/-- Weight ≤ popcount * F_{m+1} for m ≥ 1. -/
theorem weight_le_popcount_mul_fib (w : Word m) (hm : 1 ≤ m) :
    weight w ≤ popcount w * Nat.fib (m + 1) := by
  rw [weight_eq_fib_ite_sum, popcount_eq_count_true]
  -- Bound: Σ (if w i then fib(i+2) else 0) ≤ |support| * fib(m+1)
  -- = Σ_{i ∈ support} fib(m+1)
  -- Strategy: each contributing term fib(i+2) ≤ fib(m+1) since i < m
  trans (∑ i : Fin m, if w i = true then Nat.fib (m + 1) else 0)
  · apply Finset.sum_le_sum; intro i _
    by_cases hi : w i = true
    · simp [hi, Nat.fib_mono (show i.val + 2 ≤ m + 1 by omega)]
    · simp [show w i = false from by cases hw : w i <;> simp_all]
  · -- Σ (if w i = true then fib(m+1) else 0) = |support| * fib(m+1)
    trans ((Finset.univ.filter (fun i : Fin m => w i = true)).sum
        (fun _ => Nat.fib (m + 1)))
    · rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
          (p := fun i : Fin m => w i = true)
          (f := fun i : Fin m => if w i = true then Nat.fib (m + 1) else 0)]
      have h1 : ∀ i ∈ Finset.univ.filter (fun i : Fin m => w i = true),
          (if w i = true then Nat.fib (m + 1) else 0) = Nat.fib (m + 1) :=
        fun i hi => by simp [Finset.mem_filter.mp hi |>.2]
      have h2 : ∀ i ∈ Finset.univ.filter (fun i : Fin m => ¬w i = true),
          (if w i = true then Nat.fib (m + 1) else 0) = 0 :=
        fun i hi => by simp [Finset.mem_filter.mp hi |>.2]
      rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
      simp [Finset.sum_const, smul_eq_mul]
    · rw [Finset.sum_const, smul_eq_mul]

end Omega
