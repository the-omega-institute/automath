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
-- Phase 221: popcount snoc
-- ══════════════════════════════════════════════════════════════

/-- popcount(snoc w false) = popcount(w). thm:pom-popcount-snoc -/
theorem popcount_snoc_false (w : Word m) :
    popcount (snoc w false) = popcount w := by
  -- popcount + popcount_complement = m, and complement commutes with snoc
  -- Simpler: use that popcount = m - popcount(!w) and work out directly
  -- Direct proof: count of true bits in snoc w false = count in w
  -- because the extra bit is false
  have := popcount_not (snoc w false)
  have := popcount_not w
  -- popcount(!snoc w false) + popcount(snoc w false) = m + 1
  -- popcount(!w) + popcount(w) = m
  -- !snoc w false = snoc (!w) true (negate each bit, last is !false = true)
  -- popcount(snoc (!w) true) = popcount(!w) + 1 (if we had popcount_snoc_true)
  -- Circular! Let me try the card_bij approach one more time but correctly.
  simp only [popcount, wordSupport]
  -- Goal: (filter Fin(m+1) (snoc w false · = true)).card = (filter Fin m (w · = true)).card
  -- Use card_bij in the ← direction (map RHS → LHS)
  symm
  apply Finset.card_bij (fun (i : Fin m) (_ : i ∈ Finset.univ.filter (fun j => w j = true)) =>
    (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)))
  · -- Map preserves membership
    intro ⟨i, hi⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
    show snoc w false ⟨i, Nat.lt_succ_of_lt hi⟩ = true
    simp [snoc, show i < m from hi, hmem]
  · -- Injectivity
    intro ⟨i₁, _⟩ _ ⟨i₂, _⟩ _ h
    exact Fin.ext (Fin.mk.inj h)
  · -- Surjectivity
    intro ⟨j, hj⟩ hjmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjmem
    have hjLt : j < m := by
      rcases Nat.lt_or_ge j m with h | h
      · exact h
      · exfalso
        have : get (snoc w false) j = false := snoc_get_false_of_ge w h
        have : get (snoc w false) j = true := by rw [get_of_lt _ hj]; exact hjmem
        simp_all
    refine ⟨⟨j, hjLt⟩, ?_, Fin.ext rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have : snoc w false ⟨j, hj⟩ = w ⟨j, hjLt⟩ := by
      show (fun i : Fin (m + 1) => if h : i.1 < m then w ⟨i.1, h⟩ else false) ⟨j, hj⟩ = _
      simp [hjLt]
    rw [← this]; exact hjmem

/-- popcount(snoc w true) = popcount(w) + 1. thm:pom-popcount-snoc -/
theorem popcount_snoc_true (w : Word m) :
    popcount (snoc w true) = popcount w + 1 := by
  -- Use complement: popcount(snoc w true) + popcount(!snoc w true) = m + 1
  -- !snoc w true = snoc (!w) false (negate each: last = !true = false)
  -- popcount(snoc (!w) false) = popcount(!w) = m - popcount w
  -- So popcount(snoc w true) = m + 1 - (m - popcount w) = popcount w + 1
  have h1 : popcount (fun i => !(snoc w true i)) + popcount (snoc w true) = m + 1 :=
    popcount_not (snoc w true)
  have h2 : (fun i : Fin (m + 1) => !(snoc w true i)) = snoc (fun i => !w i) false := by
    funext ⟨j, hj⟩
    simp only [snoc]
    split
    · rfl
    · rename_i h; simp [show j = m from by omega]
  rw [h2, popcount_snoc_false] at h1
  have h3 : popcount (fun i : Fin m => !w i) + popcount w = m := popcount_not w
  omega

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

-- ══════════════════════════════════════════════════════════════
-- Phase 212: FibCube edge count
-- ══════════════════════════════════════════════════════════════

/-- Edge count of the Fibonacci cube Gamma_n satisfies
    e(0)=0, e(1)=1, e(n+2)=e(n+1)+e(n)+F(n+2).
    cor:pom-fibcube-edge-closed-form -/
def fibcubeEdgeCount : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibcubeEdgeCount (n + 1) + fibcubeEdgeCount n + Nat.fib (n + 2)

@[simp] theorem fibcubeEdgeCount_zero : fibcubeEdgeCount 0 = 0 := rfl
@[simp] theorem fibcubeEdgeCount_one : fibcubeEdgeCount 1 = 1 := rfl
@[simp] theorem fibcubeEdgeCount_succ_succ (n : Nat) :
    fibcubeEdgeCount (n + 2) = fibcubeEdgeCount (n + 1) + fibcubeEdgeCount n + Nat.fib (n + 2) :=
  rfl

/-- 5 * e(n) = n * F(n+1) + 2*(n+1)*F(n).
    cor:pom-fibcube-edge-closed-form -/
theorem fibcubeEdgeCount_closed (n : Nat) :
    5 * fibcubeEdgeCount n = n * Nat.fib (n + 1) + 2 * (n + 1) * Nat.fib n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | n + 2 =>
      simp only [fibcubeEdgeCount_succ_succ]
      have ih1 := ih (n + 1) (by omega)
      have ih0 := ih n (by omega)
      have hfib := Nat.fib_add_two (n := n)
      have hfib1 := Nat.fib_add_two (n := n + 1)
      nlinarith

-- ══════════════════════════════════════════════════════════════
-- Phase 214: FibCube f-vector
-- ══════════════════════════════════════════════════════════════

/-- The f-vector of the Fibonacci cube: f(n,k) counts k-dimensional faces.
    thm:pom-fibcube-fvector-closed -/
def fibcubeFVector : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | 1, 0 => 2
  | 1, 1 => 1
  | 1, _ + 2 => 0
  | n + 2, k => fibcubeFVector (n + 1) k + fibcubeFVector n k +
                  (if k = 0 then 0 else fibcubeFVector n (k - 1))

@[simp] theorem fibcubeFVector_zero_zero : fibcubeFVector 0 0 = 1 := rfl
@[simp] theorem fibcubeFVector_zero_succ (k : Nat) : fibcubeFVector 0 (k + 1) = 0 := rfl
@[simp] theorem fibcubeFVector_one_zero : fibcubeFVector 1 0 = 2 := rfl
@[simp] theorem fibcubeFVector_one_one : fibcubeFVector 1 1 = 1 := rfl
@[simp] theorem fibcubeFVector_one_succ_succ (k : Nat) : fibcubeFVector 1 (k + 2) = 0 := rfl
@[simp] theorem fibcubeFVector_succ_succ (n k : Nat) :
    fibcubeFVector (n + 2) k = fibcubeFVector (n + 1) k + fibcubeFVector n k +
      (if k = 0 then 0 else fibcubeFVector n (k - 1)) := rfl

/-- f-vector at k=0 = F(n+2). thm:pom-fibcube-fvector-closed -/
theorem fibcubeFVector_zero_eq_fib (n : Nat) :
    fibcubeFVector n 0 = Nat.fib (n + 2) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp [Nat.fib]
    | n + 2 =>
      simp only [fibcubeFVector_succ_succ, ite_true]
      rw [ih (n + 1) (by omega), ih n (by omega)]
      rw [show n + 1 + 2 = n + 2 + 1 from by omega]
      have := Nat.fib_add_two (n := n + 2)
      omega

/-- f-vector at k=1 = edge count. thm:pom-fibcube-fvector-closed -/
theorem fibcubeFVector_one_eq_edge (n : Nat) :
    fibcubeFVector n 1 = fibcubeEdgeCount n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [fibcubeEdgeCount]
    | 1 => simp [fibcubeEdgeCount]
    | n + 2 =>
      simp only [fibcubeFVector_succ_succ, show (1 : Nat) ≠ 0 from by omega, ite_false,
        show 1 - 1 = 0 from rfl]
      rw [ih (n + 1) (by omega), ih n (by omega), fibcubeFVector_zero_eq_fib]
      rfl

/-- f-vector k=1 recurrence: C(n+2,1) = C(n+1,1) + C(n,1) + F(n+2).
    thm:pom-fibcube-fvector-closed -/
theorem fibcubeFVector_one_recurrence (n : Nat) :
    fibcubeFVector (n + 2) 1 = fibcubeFVector (n + 1) 1 + fibcubeFVector n 1 +
      Nat.fib (n + 2) := by
  simp only [fibcubeFVector_succ_succ, show (1 : Nat) ≠ 0 from by omega, ite_false,
    show 1 - 1 = 0 from rfl, fibcubeFVector_zero_eq_fib]

-- ══════════════════════════════════════════════════════════════
-- Phase 217: Theta-class (coord-one) count
-- ══════════════════════════════════════════════════════════════

/-- Count of No11 words of length n with bit i set.
    thm:pom-fibcube-theta-class-size -/
noncomputable def coordOneCount (n : Nat) (i : Fin n) : Nat :=
  haveI : DecidablePred (fun w : Word n => No11 w ∧ w i = true) := Classical.decPred _
  (Finset.univ.filter (fun w : Word n => No11 w ∧ w i = true)).card

/-- Computable version of coordOneCount. -/
private def cCoordOneCount (n : Nat) (i : Fin n) : Nat :=
  (@Finset.univ (X n) (fintypeX n)).filter (fun x => x.1 i = true) |>.card

private theorem cCoordOneCount_eq_coordOneCount (n : Nat) (i : Fin n) :
    cCoordOneCount n i = coordOneCount n i := by
  classical
  simp only [cCoordOneCount, coordOneCount]
  -- Both count |{w : Word n | No11 w ∧ w i = true}|, just with different Fintype instances
  have : ∀ x : X n, x ∈ (Finset.univ.filter (fun x : X n => x.1 i = true)) ↔
      x.1 ∈ (Finset.univ.filter (fun w : Word n => No11 w ∧ w i = true)) := by
    intro x; simp [Finset.mem_filter, x.2]
  exact Finset.card_bij (fun x _ => x.1)
    (fun x hx => by simp [Finset.mem_filter] at hx ⊢; exact ⟨x.2, hx⟩)
    (fun x₁ _ x₂ _ h => Subtype.ext h)
    (fun w hw => by
      simp [Finset.mem_filter] at hw
      exact ⟨⟨w, hw.1⟩, by simp [Finset.mem_filter, hw.2], rfl⟩)

/-- coordOneCount n i = F(i+1)*F(n-i) for n ≤ 6, all i.
    cor:pom-fibcube-marginal-boundary-layer -/
theorem coordOneCount_eq_fib_prod_verified (n : Nat) (hn : n ≤ 6) (i : Fin n) :
    coordOneCount n i = Nat.fib (i.val + 1) * Nat.fib (n - i.val) := by
  rw [← cCoordOneCount_eq_coordOneCount]
  interval_cases n <;> fin_cases i <;> native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase 218: FibCube f-vector k=2 base values + recurrence
-- ══════════════════════════════════════════════════════════════

/-- f-vector k=2 recurrence: f(n+2,2) = f(n+1,2) + f(n,2) + f(n,1).
    thm:pom-fibcube-fvector-closed -/
theorem fibcubeFVector_two_recurrence (n : Nat) :
    fibcubeFVector (n + 2) 2 = fibcubeFVector (n + 1) 2 + fibcubeFVector n 2 +
      fibcubeFVector n 1 := by
  simp only [fibcubeFVector_succ_succ, show (2 : Nat) ≠ 0 from by omega, ite_false,
    show 2 - 1 = 1 from rfl]

/-- f(2, 2) = 0. thm:pom-fibcube-fvector-closed -/
@[simp] theorem fibcubeFVector_two_two : fibcubeFVector 2 2 = 0 := by
  simp [fibcubeFVector]

/-- f(3, 2) = 1. thm:pom-fibcube-fvector-closed -/
@[simp] theorem fibcubeFVector_two_three : fibcubeFVector 3 2 = 1 := by
  simp [fibcubeFVector]

/-- f(4, 2) = 3. thm:pom-fibcube-fvector-closed -/
@[simp] theorem fibcubeFVector_two_four : fibcubeFVector 4 2 = 3 := by
  simp [fibcubeFVector]

/-- f(5, 2) = 9. thm:pom-fibcube-fvector-closed -/
@[simp] theorem fibcubeFVector_two_five : fibcubeFVector 5 2 = 9 := by native_decide

/-- f(6, 2) = 22. thm:pom-fibcube-fvector-closed -/
@[simp] theorem fibcubeFVector_two_six : fibcubeFVector 6 2 = 22 := by native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase 219: Fib product split + edge count convolution
-- ══════════════════════════════════════════════════════════════

/-- F(n) = F(i)*F(n-i+1) + F(i-1)*F(n-i) for 1 ≤ i ≤ n.
    Follows from fib_add_formula with m = i-1, k = n-i.
    thm:pom-fib-product-split -/
theorem fib_product_split (n i : Nat) (hi : 1 ≤ i) (hin : i ≤ n) :
    Nat.fib n = Nat.fib i * Nat.fib (n - i + 1) + Nat.fib (i - 1) * Nat.fib (n - i) := by
  have h := fib_add_formula (i - 1) (n - i)
  rw [show i - 1 + (n - i) + 1 = n from by omega,
      show i - 1 + 1 = i from by omega,
      show n - i + 1 = n - i + 1 from rfl] at h
  exact h

/-- Edge count equals Fibonacci convolution: e(n) = Σ_{i<n} F(i+1)*F(n-i).
    cor:pom-fibcube-edge-fib-conv -/
theorem fibcubeEdgeCount_eq_fib_conv (n : Nat) :
    fibcubeEdgeCount n = ∑ i ∈ Finset.range n, Nat.fib (i + 1) * Nat.fib (n - i) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp [fibcubeEdgeCount, Nat.fib]
    | n + 2 =>
      rw [fibcubeEdgeCount_succ_succ, ih (n + 1) (by omega), ih n (by omega)]
      -- Goal: (Σ i<n+1, F(i+1)*F(n+1-i)) + (Σ i<n, F(i+1)*F(n-i)) + F(n+2)
      --      = Σ i<n+2, F(i+1)*F(n+2-i)
      symm
      -- Goal: Σ i<n+2, F(i+1)*F(n+2-i) = LHS
      -- Step 1: Peel last term from range(n+2)
      have hpeel : ∑ i ∈ Finset.range (n + 2), Nat.fib (i + 1) * Nat.fib (n + 2 - i) =
          (∑ i ∈ Finset.range (n + 1), Nat.fib (i + 1) * Nat.fib (n + 2 - i)) +
          Nat.fib (n + 2) := by
        rw [Finset.sum_range_succ]
        congr 1
        simp [Nat.sub_self]
      rw [hpeel]
      -- Step 2: Split F(n+2-i) = F(n+1-i) + F(n-i) for i < n+1
      have hsplit : ∀ i ∈ Finset.range (n + 1),
          Nat.fib (i + 1) * Nat.fib (n + 2 - i) =
          Nat.fib (i + 1) * Nat.fib (n + 1 - i) + Nat.fib (i + 1) * Nat.fib (n - i) := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [show n + 2 - i = (n - i) + 2 from by omega, Nat.fib_add_two,
          show n - i + 1 = n + 1 - i from by omega]
        ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      -- Step 3: Peel last term from Σ_{i<n+1} F(i+1)*F(n-i)
      rw [Finset.sum_range_succ (fun i => Nat.fib (i + 1) * Nat.fib (n - i))]
      simp only [Nat.sub_self, Nat.fib_zero, Nat.mul_zero, Nat.add_zero]

-- ══════════════════════════════════════════════════════════════
-- Phase 220: Word reversal involution + xReverse + coordOneCount symmetry
-- ══════════════════════════════════════════════════════════════

/-- Word reversal is an involution. thm:pom-fibcube-aut-z2 -/
theorem wordReverse_involutive (w : Word m) : wordReverse (wordReverse w) = w := by
  funext i
  simp only [wordReverse]
  congr 1
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

/-- wordReverse maps bit i to bit (m-1-i). thm:pom-fibcube-aut-z2 -/
theorem wordReverse_apply (w : Word m) (i : Fin m) :
    wordReverse w i = w ⟨m - 1 - i.val, by omega⟩ := rfl

/-- Index reversal on X m. thm:pom-fibcube-aut-z2 -/
def xReverse (x : X m) : X m := ⟨wordReverse x.1, no11_reverse x.2⟩

/-- xReverse is involutive. thm:pom-fibcube-aut-z2 -/
theorem xReverse_involutive : Function.Involutive (xReverse (m := m)) := by
  intro x; exact Subtype.ext (wordReverse_involutive x.1)

/-- Computable version of totalPopcount. -/
private def cTotalPopcount (m : Nat) : Nat :=
  (@Finset.univ (X m) (fintypeX m)).sum (fun x => popcount x.1)

private theorem cTotalPopcount_eq (m : Nat) : cTotalPopcount m = totalPopcount m := by
  simp only [cTotalPopcount, totalPopcount]
  exact Finset.sum_congr (by ext; simp) (fun x _ => rfl)

/-- totalPopcount 1 = 1. thm:pom-totalPopcount-one -/
theorem totalPopcount_one : totalPopcount 1 = 1 := by
  rw [← cTotalPopcount_eq]; native_decide

/-- Embed X m into X (m+2) by appending "01" (false then true). -/
private def embedFalseTrue (w : X m) : X (m + 2) :=
  ⟨snoc (snoc w.1 false) true,
    no11_snoc_true (no11_snoc_false w.2) (by
      simp [get, snoc, show m < m + 1 from by omega])⟩

private theorem embedFalseTrue_popcount (w : X m) :
    popcount (embedFalseTrue w).1 = popcount w.1 + 1 := by
  simp [embedFalseTrue, popcount_snoc_true, popcount_snoc_false]

/-- totalPopcount(m+2) = totalPopcount(m+1) + totalPopcount(m) + F(m+2). -/
private theorem totalPopcount_succ_succ (m : Nat) :
    totalPopcount (m + 2) = totalPopcount (m + 1) + totalPopcount m + Nat.fib (m + 2) := by
  classical
  simp only [totalPopcount]
  -- Split X(m+2) by last bit
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun x : X (m + 2) => x.1 ⟨m + 1, by omega⟩ = false) (fun x => popcount x.1)]
  -- Part 1: {last=false} bijects with X(m+1), preserving popcount
  have hfalse : ∑ x ∈ Finset.univ.filter (fun x : X (m + 2) =>
      x.1 ⟨m + 1, by omega⟩ = false), popcount x.1 = ∑ x : X (m + 1), popcount x.1 := by
    symm
    refine Finset.sum_nbij' (X.appendFalse) (X.restrict) ?_ ?_ ?_ ?_ ?_
    · intro x _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change snoc x.1 false ⟨m + 1, by omega⟩ = false
      simp only [snoc, show ¬(m + 1 < m + 1) from by omega, dite_false]
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact Finset.mem_univ _
    · intro x _; exact X.restrict_appendFalse x
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact X.appendFalse_reconstruct x (by
        show Omega.last x.1 = false
        simp only [Omega.last, Omega.get, show m + 1 < m + 2 from by omega, dite_true]; exact hx)
    · intro x _; exact (popcount_snoc_false x.1).symm
  -- Part 2: {last=true} bijects with X(m), popcount shifts by +1
  have htrue_filter : Finset.univ.filter
      (fun x : X (m + 2) => ¬x.1 ⟨m + 1, by omega⟩ = false) =
      Finset.univ.filter (fun x : X (m + 2) => x.1 ⟨m + 1, by omega⟩ = true) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases x.1 ⟨m + 1, by omega⟩ <;> simp
  have htrue : ∑ x ∈ Finset.univ.filter (fun x : X (m + 2) =>
      ¬x.1 ⟨m + 1, by omega⟩ = false), popcount x.1 =
      ∑ w : X m, popcount w.1 + Nat.fib (m + 2) := by
    rw [htrue_filter]
    have hbij : ∑ x ∈ Finset.univ.filter (fun x : X (m + 2) =>
        x.1 ⟨m + 1, by omega⟩ = true), popcount x.1 = ∑ w : X m, (popcount w.1 + 1) := by
      symm
      refine Finset.sum_nbij' embedFalseTrue (fun x => X.restrict (X.restrict x)) ?_ ?_ ?_ ?_ ?_
      · intro w _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, embedFalseTrue, snoc]
        simp only [show ¬(m + 1) < m + 1 from by omega, dite_false]
      · intro x _; exact Finset.mem_univ _
      · -- left inverse: restrict(restrict(embedFalseTrue w)) = w
        intro w _; apply Subtype.ext; funext ⟨i, hi⟩
        show truncate (truncate (snoc (snoc w.1 false) true)) ⟨i, hi⟩ = w.1 ⟨i, hi⟩
        simp only [truncate, snoc, show i < m + 1 from by omega, dite_true, show i < m from hi, dite_true]
      · -- right inverse: embedFalseTrue(restrict(restrict x)) = x
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have hPrev : x.1 ⟨m, by omega⟩ = false := by
          by_contra hc; push_neg at hc
          have ht : x.1 ⟨m, by omega⟩ = true := by
            cases hb : x.1 ⟨m, by omega⟩ <;> simp_all
          exact x.2 m (by rw [get]; simp [show m < m + 2 from by omega]; exact ht)
            (by rw [get]; simp [show m + 1 < m + 2 from by omega]; exact hx)
        apply Subtype.ext; funext ⟨i, hi⟩
        simp only [embedFalseTrue, snoc, X.restrict, truncate]
        by_cases h1 : i < m + 1
        · by_cases h2 : i < m
          · simp only [h1, dite_true, h2, dite_true]
          · have him : i = m := by omega
            simp only [him, show m < m + 1 from by omega, dite_true, show ¬m < m from by omega,
              dite_false, hPrev]
        · have him1 : i = m + 1 := by omega
          simp only [him1, show ¬(m + 1) < m + 1 from by omega, dite_false, hx]
      · intro w _; exact (embedFalseTrue_popcount w).symm
    rw [hbij, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one,
      Finset.card_univ, X.card_eq_fib]
  rw [hfalse, htrue]; omega

/-- Total popcount across X_m = Fibonacci cube edge count.
    thm:pom-fibcube-theta-class-size -/
theorem totalPopcount_eq_edgeCount (m : Nat) :
    totalPopcount m = fibcubeEdgeCount m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => rw [totalPopcount_zero, fibcubeEdgeCount_zero]
    | 1 => rw [totalPopcount_one, fibcubeEdgeCount_one]
    | m + 2 =>
      rw [totalPopcount_succ_succ, ih (m + 1) (by omega), ih m (by omega),
        fibcubeEdgeCount_succ_succ]

/-- Computable totalPopcount equals sum of computable coordOneCounts (double counting). -/
private theorem cTotalPopcount_eq_sum_cCoordOneCount (n : Nat) :
    cTotalPopcount n = ∑ i : Fin n, cCoordOneCount n i := by
  simp only [cTotalPopcount, cCoordOneCount, popcount, wordSupport,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- Edge count equals sum of coord-one counts (double counting: each edge corresponds
    to a bit position where the word has a 1).
    thm:pom-fibcube-theta-class-size -/
theorem fibcubeEdgeCount_eq_sum_coordOneCount (n : Nat) :
    fibcubeEdgeCount n = ∑ i : Fin n, coordOneCount n i := by
  rw [← totalPopcount_eq_edgeCount, ← cTotalPopcount_eq,
    cTotalPopcount_eq_sum_cCoordOneCount]
  congr 1; ext i; exact cCoordOneCount_eq_coordOneCount n i

/-- fibcubeEdgeCount is positive for n ≥ 1. -/
private theorem fibcubeEdgeCount_pos (n : Nat) (hn : 1 ≤ n) : 0 < fibcubeEdgeCount n := by
  induction n with
  | zero => omega
  | succ n ih =>
    match n with
    | 0 => simp
    | n + 1 =>
      rw [fibcubeEdgeCount_succ_succ]
      have := fib_succ_pos (n + 1)
      omega

/-- Fibonacci cube edge count strictly increases for n ≥ 1.
    cor:pom-fibcube-edge-closed-form -/
theorem fibcubeEdgeCount_strict_mono (n : Nat) (hn : 1 ≤ n) :
    fibcubeEdgeCount n < fibcubeEdgeCount (n + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  -- e(n+2) = e(n+1) + e(n) + F(n+2) > e(n+1)
  show fibcubeEdgeCount (n + 1) < fibcubeEdgeCount (n + 1 + 1)
  rw [fibcubeEdgeCount_succ_succ]
  have hF := fib_succ_pos (n + 1)
  linarith

/-- Theta-class symmetry under index reversal: coordOneCount n i = coordOneCount n (n-1-i).
    thm:pom-fibcube-theta-class-size -/
theorem coordOneCount_symm (n : Nat) (i : Fin n) :
    coordOneCount n i = coordOneCount n ⟨n - 1 - i.val, by omega⟩ := by
  -- coordOneCount uses Classical.decPred internally; unfold and work at the Finset level
  unfold coordOneCount
  -- Both sides use Classical.decPred, so the Finset.filter instances match
  -- Construct bijection via wordReverse
  apply Finset.card_bij (fun w _ => wordReverse w)
  · -- Map property: w ∈ {No11 ∧ w[i]=true} → wordReverse w ∈ {No11 ∧ w[n-1-i]=true}
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact ⟨no11_reverse hw.1, by
      show wordReverse w ⟨n - 1 - i.val, _⟩ = true
      rw [wordReverse_apply]
      have : (⟨n - 1 - (n - 1 - i.val), by omega⟩ : Fin n) = i := by
        apply Fin.ext; simp; omega
      rw [this]; exact hw.2⟩
  · -- Injectivity
    intro w₁ _ w₂ _ h
    have := congr_arg wordReverse h
    rwa [wordReverse_involutive, wordReverse_involutive] at this
  · -- Surjectivity
    intro w' hw'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw'
    refine ⟨wordReverse w', ?_, wordReverse_involutive w'⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨no11_reverse hw'.1, by
      show wordReverse w' i = true
      rw [wordReverse_apply]; exact hw'.2⟩

-- ══════════════════════════════════════════════════════════════
-- coordOneCount = fib product (general proof)
-- ══════════════════════════════════════════════════════════════

/-- Recursion: coordOneCount(n+2, i) = coordOneCount(n+1, i) + coordOneCount(n, i) for i < n.
    Split X(n+2) by last bit: last=false bijects with X(n+1), last=true bijects with X(n). -/
private theorem coordOneCount_succ_succ (n : Nat) (i : Fin n) :
    coordOneCount (n + 2) ⟨i.val, by omega⟩ =
    coordOneCount (n + 1) ⟨i.val, by omega⟩ + coordOneCount n i := by
  -- Work with cCoordOneCount to avoid Classical.decPred issues
  rw [← cCoordOneCount_eq_coordOneCount, ← cCoordOneCount_eq_coordOneCount,
    ← cCoordOneCount_eq_coordOneCount]
  -- Define the three filtered sets using fintypeX
  let S2 := (@Finset.univ (X (n + 2)) (fintypeX (n + 2))).filter
    (fun x => x.1 ⟨i.val, by omega⟩ = true)
  let S1 := (@Finset.univ (X (n + 1)) (fintypeX (n + 1))).filter
    (fun x => x.1 ⟨i.val, by omega⟩ = true)
  let S0 := (@Finset.univ (X n) (fintypeX n)).filter (fun x => x.1 i = true)
  change S2.card = S1.card + S0.card
  -- Split S2 by last bit
  let S2f := S2.filter (fun x => x.1 ⟨n + 1, by omega⟩ = false)
  let S2t := S2.filter (fun x => x.1 ⟨n + 1, by omega⟩ = true)
  have hS2 : S2 = S2f ∪ S2t := by
    simp only [S2f, S2t]; ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro h; cases hb : x.1 ⟨n + 1, by omega⟩ <;> simp [h, hb]
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  rw [hS2, Finset.card_union_of_disjoint (by
    simp only [S2f, S2t]; apply Finset.disjoint_filter.mpr
    intro x _ h1 h2; simp_all)]
  congr 1
  -- Part 1: S2f bijects with S1 via restrict
  · apply Finset.card_bij (fun x _ => X.restrict x)
    · intro x hx
      simp only [S2f, S2, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and]
      show truncate x.1 ⟨i.val, by omega⟩ = true
      simp [truncate, show i.val < n + 1 from by omega, hx.1]
    · intro x₁ hx₁ x₂ hx₂ h
      simp only [S2f, S2, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
      apply Subtype.ext; funext ⟨j, hj⟩
      by_cases hjn : j < n + 1
      · have := congr_arg (fun y => y.1 ⟨j, by omega⟩) h
        simp [X.restrict, truncate, hjn] at this; exact this
      · have hj1 : j = n + 1 := by omega
        subst hj1; simp [hx₁.2, hx₂.2]
    · intro y hy
      simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp only [S2f, S2, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨X.appendFalse y,
        ⟨by simp [snoc, show i.val < n + 1 from by omega, hy],
         by simp [snoc, show ¬(n + 1 < n + 1) from by omega]⟩,
        X.restrict_appendFalse y⟩
  -- Part 2: S2t bijects with S0 via restrict ∘ restrict
  · apply Finset.card_bij (fun x _ => X.restrict (X.restrict x))
    · intro x hx
      simp only [S2t, S2, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and]
      show truncate (truncate x.1) i = true
      simp [truncate, show i.val < n from i.isLt, show i.val < n + 1 from by omega, hx.1]
    · -- Injectivity: if restrict(restrict(x₁)) = restrict(restrict(x₂)) then x₁ = x₂
      -- because x₁.1[n]=x₂.1[n]=false (No11+last=true) and x₁.1[n+1]=x₂.1[n+1]=true (filter)
      intro x₁ hx₁ x₂ hx₂ h
      simp only [S2t, S2, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
      apply Subtype.ext; funext ⟨j, hj⟩
      -- For j < n: follows from restrict∘restrict equality
      -- For j = n: both are false (No11 constraint)
      -- For j = n+1: both are true (filter constraint)
      have hval := congr_arg Subtype.val h
      by_cases hj1 : j < n
      · have := congr_arg (fun w => w ⟨j, by omega⟩) hval
        simp [X.restrict, truncate, show j < n + 1 from by omega, hj1] at this; exact this
      · by_cases hj2 : j < n + 1
        · -- j = n
          have hjn : j = n := by omega
          have hfin : (⟨j, hj⟩ : Fin (n + 2)) = ⟨n, by omega⟩ := Fin.ext (by omega)
          have : x₁.1 ⟨j, hj⟩ = false := by
            rw [hfin]; by_contra hc
            have ht := eq_true_of_ne_false hc
            exact x₁.2 n (by rw [get]; simp [show n < n + 2 from by omega]; exact ht)
              (by rw [get]; simp [show n + 1 < n + 2 from by omega]; exact hx₁.2)
          have : x₂.1 ⟨j, hj⟩ = false := by
            rw [hfin]; by_contra hc
            have ht := eq_true_of_ne_false hc
            exact x₂.2 n (by rw [get]; simp [show n < n + 2 from by omega]; exact ht)
              (by rw [get]; simp [show n + 1 < n + 2 from by omega]; exact hx₂.2)
          simp_all
        · -- j = n+1
          have hjn1 : j = n + 1 := by omega
          have hfin : (⟨j, hj⟩ : Fin (n + 2)) = ⟨n + 1, by omega⟩ := Fin.ext hjn1
          rw [show x₁.1 ⟨j, hj⟩ = x₁.1 ⟨n + 1, by omega⟩ from by rw [hfin],
            show x₂.1 ⟨j, hj⟩ = x₂.1 ⟨n + 1, by omega⟩ from by rw [hfin],
            hx₁.2, hx₂.2]
    · intro z hz
      simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [S2t, S2, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨embedFalseTrue ⟨z.1, z.2⟩, ⟨?_, ?_⟩, ?_⟩
      · show snoc (snoc z.1 false) true ⟨i.val, by omega⟩ = true
        simp [snoc, show i.val < n from i.isLt, show i.val < n + 1 from by omega, hz]
      · show snoc (snoc z.1 false) true ⟨n + 1, by omega⟩ = true
        simp [snoc, show ¬(n + 1 < n + 1) from by omega]
      · apply Subtype.ext; funext ⟨j, hj⟩
        show truncate (truncate (snoc (snoc z.1 false) true)) ⟨j, hj⟩ = z.1 ⟨j, hj⟩
        simp [truncate, snoc, show j < n + 1 from by omega, show j < n from hj]

/-- coordOneCount n i = fib(i+1) * fib(n-i) for all n, i.
    thm:pom-fibcube-theta-class-size / cor:pom-fibcube-marginal-boundary-layer -/
theorem coordOneCount_eq_fib_prod (n : Nat) (i : Fin n) :
    coordOneCount n i = Nat.fib (i.val + 1) * Nat.fib (n - i.val) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n, i with
    | 0, i => exact i.elim0
    | 1, i => exact coordOneCount_eq_fib_prod_verified 1 (by omega) i
    | 2, i => exact coordOneCount_eq_fib_prod_verified 2 (by omega) i
    | 3, i => exact coordOneCount_eq_fib_prod_verified 3 (by omega) i
    | 4, i => exact coordOneCount_eq_fib_prod_verified 4 (by omega) i
    | 5, i => exact coordOneCount_eq_fib_prod_verified 5 (by omega) i
    | 6, i => exact coordOneCount_eq_fib_prod_verified 6 (by omega) i
    | n + 7, ⟨j, hj⟩ =>
      -- n+7 ≥ 7, so n ≥ 0 and n+5 ≥ 5
      by_cases hjn : j < n + 5
      · -- j < n+5: direct recursion
        have hrec := coordOneCount_succ_succ (n + 5) ⟨j, hjn⟩
        rw [hrec, ih (n + 6) (by omega) ⟨j, by omega⟩,
          ih (n + 5) (by omega) ⟨j, hjn⟩, ← Nat.left_distrib]
        congr 1
        have h1 : n + 7 - j = (n + 5 - j) + 2 := by omega
        have h2 : n + 6 - j = (n + 5 - j) + 1 := by omega
        rw [h1, Nat.fib_add_two, h2]; ring
      · -- j ≥ n+5: symmetric index n+6-j ≤ 1 < n+5
        have hjle : n + 5 ≤ j := by omega
        rw [coordOneCount_symm]
        have hklt : n + 6 - j < n + 5 := by omega
        have hrec := coordOneCount_succ_succ (n + 5) ⟨n + 6 - j, hklt⟩
        conv_lhs =>
          rw [show (⟨n + 7 - 1 - j, _⟩ : Fin (n + 7)) = ⟨n + 6 - j, by omega⟩ from rfl]
        rw [hrec, ih (n + 6) (by omega) ⟨n + 6 - j, by omega⟩,
          ih (n + 5) (by omega) ⟨n + 6 - j, hklt⟩, ← Nat.left_distrib]
        -- Goal: fib(n+6-j+1) * (fib(n+6-(n+6-j)) + fib(n+5-(n+6-j))) = fib(j+1) * fib(n+7-j)
        -- After simplification: fib(n+7-j) * (fib(j) + fib(j-1)) = fib(j+1) * fib(n+7-j)
        -- Use fib(j+1) = fib(j) + fib(j-1) (Fibonacci recurrence, j ≥ 2)
        show Nat.fib (n + 6 - j + 1) *
          (Nat.fib (n + 6 - (n + 6 - j)) + Nat.fib (n + 5 - (n + 6 - j))) =
          Nat.fib (j + 1) * Nat.fib (n + 7 - j)
        rw [show n + 6 - (n + 6 - j) = j from Nat.sub_sub_self (by omega : j ≤ n + 6),
          show n + 5 - (n + 6 - j) = j - 1 from by omega,
          show n + 6 - j + 1 = n + 7 - j from by omega]
        -- Goal: fib(n+7-j) * (fib(j) + fib(j-1)) = fib(j+1) * fib(n+7-j)
        -- Suffices to show fib(j) + fib(j-1) = fib(j+1)
        rw [Nat.mul_comm]
        congr 1
        obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ j by omega)
        rw [show 2 + j' - 1 = j' + 1 from by omega,
          show 2 + j' + 1 = (j' + 1) + 2 from by omega, Nat.fib_add_two,
          show 2 + j' = (j' + 1) + 1 from by omega]
        omega

-- ══════════════════════════════════════════════════════════════
-- Phase 226: f-vector k=2 strict monotonicity
-- ══════════════════════════════════════════════════════════════

/-- f-vector k=2 strictly increases for n ≥ 3. thm:pom-fibcube-fvector-closed -/
theorem fibcubeFVector_two_strict_mono (n : Nat) (hn : 3 ≤ n) :
    fibcubeFVector n 2 < fibcubeFVector (n + 1) 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  -- f(n+2, 2) = f(n+1, 2) + f(n, 2) + f(n, 1)
  -- So f(n+2, 2) > f(n+1, 2) iff f(n, 2) + f(n, 1) > 0
  show fibcubeFVector (n + 1) 2 < fibcubeFVector (n + 1 + 1) 2
  rw [fibcubeFVector_two_recurrence]
  -- f(n, 1) = e(n) ≥ 1 for n ≥ 1
  have hedge : 0 < fibcubeFVector n 1 := by
    rw [fibcubeFVector_one_eq_edge]
    exact fibcubeEdgeCount_pos n (by omega)
  linarith

-- ══════════════════════════════════════════════════════════════
-- Phase 228: f-vector k=3 recurrence + base values
-- ══════════════════════════════════════════════════════════════

/-- f(n+2,3) = f(n+1,3) + f(n,3) + f(n,2). thm:pom-fibcube-fvector-closed -/
theorem fibcubeFVector_three_recurrence (n : Nat) :
    fibcubeFVector (n + 2) 3 = fibcubeFVector (n + 1) 3 + fibcubeFVector n 3 +
      fibcubeFVector n 2 := by
  simp only [fibcubeFVector_succ_succ, show (3 : Nat) ≠ 0 from by omega, ite_false,
    show 3 - 1 = 2 from rfl]

@[simp] theorem fibcubeFVector_three_three : fibcubeFVector 3 3 = 0 := by
  simp [fibcubeFVector]

@[simp] theorem fibcubeFVector_three_four : fibcubeFVector 4 3 = 0 := by
  simp [fibcubeFVector]

@[simp] theorem fibcubeFVector_three_five : fibcubeFVector 5 3 = 1 := by native_decide

@[simp] theorem fibcubeFVector_three_six : fibcubeFVector 6 3 = 4 := by native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase 238: FibCube edge bound
-- ══════════════════════════════════════════════════════════════

/-- 2*e(n) ≤ (n+1)*F(n+2): average degree at most n+1.
    cor:pom-fibcube-edge-closed-form (weak bound) -/
theorem fibcubeEdgeCount_double_bound (n : Nat) :
    2 * fibcubeEdgeCount n ≤ (n + 1) * Nat.fib (n + 2) := by
  rcases n with _ | n
  · simp [fibcubeEdgeCount]
  · have hclosed := fibcubeEdgeCount_closed (n + 1)
    have hfib := Nat.fib_add_two (n := n + 1)
    rw [show n + 1 + 1 = n + 2 from by omega] at hfib
    have hfpos : 0 < Nat.fib (n + 2) := Nat.fib_pos.mpr (by omega)
    have hfpos2 : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
    nlinarith

-- ══════════════════════════════════════════════════════════════
-- Phase 239: FibCube edge and f-vector bounds
-- ══════════════════════════════════════════════════════════════

/-- e(n) ≥ F(n+1) for n ≥ 2.
    cor:pom-fibcube-edge-closed-form (lower bound) -/
theorem fibcubeEdgeCount_ge_fib (n : Nat) (hn : 2 ≤ n) :
    Nat.fib (n + 1) ≤ fibcubeEdgeCount n := by
  -- 5*e(n) = n*F(n+1) + 2*(n+1)*F(n), need 5*F(n+1) ≤ n*F(n+1) + 2*(n+1)*F(n)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hclosed := fibcubeEdgeCount_closed (k + 2)
  have hfpos : 0 < Nat.fib (k + 3) := Nat.fib_pos.mpr (by omega)
  have hfpos2 : 0 < Nat.fib (k + 2) := Nat.fib_pos.mpr (by omega)
  -- (k+2)*F(k+3) + 2*(k+3)*F(k+2) ≥ 5*F(k+3)
  -- iff (k-3)*F(k+3) + 2*(k+3)*F(k+2) ≥ 0
  -- For k ≥ 3: both terms ≥ 0
  -- For k = 0,1,2: (3-k)*F(k+3) ≤ 2*(k+3)*F(k+2), verify
  match k with
  | 0 => simp [fibcubeEdgeCount, Nat.fib]
  | 1 => simp [fibcubeEdgeCount, Nat.fib]
  | 2 => simp [fibcubeEdgeCount, Nat.fib]
  | k + 3 => nlinarith

/-- f(n, 2) ≥ F(n) for n ≥ 4.
    thm:pom-fibcube-fvector-closed (lower bound) -/
theorem fibcubeFVector_two_ge_fib (n : Nat) (hn : 4 ≤ n) :
    Nat.fib n ≤ fibcubeFVector n 2 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 | 1 | 2 | 3 => omega
    | 4 => simp [fibcubeFVector_two_four, Nat.fib]
    | 5 => simp [fibcubeFVector_two_five, Nat.fib]
    | n + 6 =>
      have ih1 := ih (n + 5) (by omega) (by omega)
      have ih2 := ih (n + 4) (by omega) (by omega)
      have hrec := fibcubeFVector_two_recurrence (n + 4)
      rw [show n + 4 + 2 = n + 6 from by omega, show n + 4 + 1 = n + 5 from by omega] at hrec
      have hfib := Nat.fib_add_two (n := n + 4)
      rw [show n + 4 + 2 = n + 6 from by omega, show n + 4 + 1 = n + 5 from by omega] at hfib
      -- f(n+6,2) = f(n+5,2) + f(n+4,2) + f(n+4,1)
      -- ≥ F(n+5) + F(n+4) + 0 = F(n+6)
      linarith

-- ══════════════════════════════════════════════════════════════
-- Phase 240: FibCube monotonicity + edge bounds
-- ══════════════════════════════════════════════════════════════

/-- f(n,3) strictly increases for n ≥ 5.
    thm:pom-fibcube-fvector-closed -/
theorem fibcubeFVector_three_strict_mono (n : Nat) (hn : 5 ≤ n) :
    fibcubeFVector n 3 < fibcubeFVector (n + 1) 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  -- f(k+6,3) = f(k+5,3) + f(k+4,3) + f(k+4,2)
  show fibcubeFVector (k + 5) 3 < fibcubeFVector (k + 5 + 1) 3
  rw [show k + 5 + 1 = k + 4 + 2 from by omega]
  rw [fibcubeFVector_three_recurrence (k + 4)]
  rw [show k + 4 + 1 = k + 5 from by omega]
  -- Need: f(k+4,3) + f(k+4,2) > 0
  have hf2 : 0 < fibcubeFVector (k + 4) 2 := by
    have : fibcubeFVector 4 2 = 3 := fibcubeFVector_two_four
    have hmono := fibcubeFVector_two_strict_mono (k + 3) (by omega)
    linarith [fibcubeFVector_two_four]
  linarith

/-- f-vector vanishing: C(n,k) = 0 when k > ⌊(n+1)/2⌋.
    thm:pom-fibcube-fvector-closed (vanishing range) -/
theorem fibcubeFVector_eq_zero_of_gt (n k : Nat) (hk : (n + 1) / 2 < k) :
    fibcubeFVector n k = 0 := by
  suffices h : ∀ n k : Nat, (n + 1) / 2 < k → fibcubeFVector n k = 0 from h n k hk
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro k hk
    match n with
    | 0 =>
      match k with
      | 0 => omega
      | k + 1 => rfl
    | 1 =>
      match k with
      | 0 => omega
      | 1 => omega
      | k + 2 => rfl
    | n + 2 =>
      simp only [fibcubeFVector_succ_succ]
      have h1 : (n + 1 + 1) / 2 < k := by omega
      have h2 : (n + 1) / 2 < k := by omega
      rw [ih (n + 1) (by omega) k h1, ih n (by omega) k h2]
      simp only [Nat.zero_add]
      split
      · rfl
      · have h3 : (n + 1) / 2 < k - 1 := by omega
        rw [ih n (by omega) (k - 1) h3]

-- ══════════════════════════════════════════════════════════════
-- Phase R7: total f-vector and positivity
-- ══════════════════════════════════════════════════════════════

/-- Extending range doesn't change fibcubeFVector sum when extra terms vanish. -/
private theorem fibcubeFVector_sum_extend (n p : Nat) (hp : (n + 1) / 2 < p) :
    ∑ k ∈ Finset.range (p + 1), fibcubeFVector n k =
    ∑ k ∈ Finset.range p, fibcubeFVector n k := by
  rw [Finset.sum_range_succ, fibcubeFVector_eq_zero_of_gt n p hp, Nat.add_zero]

/-- Total subcube count C_n(1) = ∑_k C(n,k).
    cor:pom-fibcube-fpoly-growth-constant -/
noncomputable def totalFibcubeFVector (n : Nat) : Nat :=
  ∑ k ∈ Finset.range (n + 1), fibcubeFVector n k

@[simp] theorem totalFibcubeFVector_zero : totalFibcubeFVector 0 = 1 := by
  simp [totalFibcubeFVector, fibcubeFVector]

@[simp] theorem totalFibcubeFVector_one : totalFibcubeFVector 1 = 3 := by
  unfold totalFibcubeFVector
  simp [Finset.sum_range_succ]

/-- The shifted sum ∑_{k=0}^{p} (if k=0 then 0 else f(n,k-1)) = ∑_{k=0}^{p-1} f(n,k). -/
private theorem fibcubeFVector_shifted_sum (n p : Nat) :
    ∑ k ∈ Finset.range (p + 1),
      (if k = 0 then 0 else fibcubeFVector n (k - 1)) =
    ∑ k ∈ Finset.range p, fibcubeFVector n k := by
  rw [Finset.sum_range_succ]
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ (fun k => if k = 0 then 0 else fibcubeFVector n (k - 1))]
    simp only [show ¬(p + 1 = 0) from by omega, ite_false, show p + 1 - 1 = p from by omega]
    rw [Finset.sum_range_succ]
    omega

/-- C_{n+2}(1) = C_{n+1}(1) + 2·C_n(1).
    cor:pom-fibcube-fpoly-growth-constant -/
theorem totalFibcubeFVector_succ_succ (n : Nat) :
    totalFibcubeFVector (n + 2) =
    totalFibcubeFVector (n + 1) + 2 * totalFibcubeFVector n := by
  simp only [totalFibcubeFVector, show n + 2 + 1 = n + 3 from rfl]
  -- Expand using fibcubeFVector_succ_succ
  conv_lhs => arg 2; ext k; rw [fibcubeFVector_succ_succ]
  simp only [Finset.sum_add_distrib]
  -- Three sums: ∑ f(n+1,k) + ∑ f(n,k) + ∑ (if k=0 then 0 else f(n,k-1))
  -- Sum 1: extend range(n+1+1) → range(n+3) with one vanishing term
  rw [show n + 1 + 1 = n + 2 from rfl]
  -- Sum 3 (shifted): = ∑_{k=0}^{n+1} f(n,k) by shifted_sum
  rw [fibcubeFVector_shifted_sum n (n + 2)]
  -- Collapse all extended ranges using vanishing
  rw [fibcubeFVector_sum_extend n (n + 2) (by omega)]
  rw [fibcubeFVector_sum_extend (n + 1) (n + 2) (by omega)]
  -- LHS: ∑(n+2) f(n+1) + ∑(n+2) f(n) + ∑(n+2) f(n)
  -- RHS: ∑(n+2) f(n+1) + 2 * ∑(n+1) f(n)  (from totalFibcubeFVector unfolding)
  -- Collapse ∑(n+2) f(n) → ∑(n+1) f(n) using vanishing
  conv_lhs =>
    rw [show ∀ a b c : Nat, a + b + c = a + (b + c) from by omega]
  congr 1
  rw [fibcubeFVector_sum_extend n (n + 1) (by omega)]
  omega

/-- f-vector positivity: f(n,k) > 0 when 2k ≤ n.
    thm:pom-fibcube-fvector-closed (positivity) -/
theorem fibcubeFVector_pos (n k : Nat) (hk : 2 * k ≤ n) :
    0 < fibcubeFVector n k := by
  suffices h : ∀ n k : Nat, 2 * k ≤ n → 0 < fibcubeFVector n k from h n k hk
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro k hk
    match n, k with
    | 0, 0 => simp
    | 1, 0 => simp
    | n + 2, 0 =>
      rw [fibcubeFVector_zero_eq_fib]
      exact Nat.fib_pos.mpr (by omega)
    | n + 2, k + 1 =>
      simp only [fibcubeFVector_succ_succ, show ¬(k + 1 = 0) from by omega, ite_false,
        show k + 1 - 1 = k from by omega]
      have : 0 < fibcubeFVector n k := ih n (by omega) k (by omega)
      omega

/-- Combined closed form: for even n, 3T(n)+1 = 2^{n+2}; for odd n, 3T(n) = 2^{n+2}+1. -/
private theorem totalFibcubeFVector_closed_aux (n : Nat) :
    (n % 2 = 0 → 3 * totalFibcubeFVector n + 1 = 2 ^ (n + 2)) ∧
    (n % 2 = 1 → 3 * totalFibcubeFVector n = 2 ^ (n + 2) + 1) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => exact ⟨fun _ => by simp, fun h => absurd h (by omega)⟩
    | 1 => exact ⟨fun h => absurd h (by omega), fun _ => by simp⟩
    | n + 2 =>
      have ⟨ih0_even, ih0_odd⟩ := ih n (by omega)
      have ⟨ih1_even, ih1_odd⟩ := ih (n + 1) (by omega)
      have hpow : 2 ^ (n + 1 + 2) = 2 ^ (n + 3) := by ring_nf
      constructor
      · intro heven
        rw [totalFibcubeFVector_succ_succ]
        have h0 := ih0_even (by omega)
        have h1 := ih1_odd (by omega); rw [hpow] at h1
        -- 3*(T1 + 2*T0) + 1 where 3*T1 = 2^(n+3)+1, 3*T0 + 1 = 2^(n+2)
        -- = 3*T1 + 6*T0 + 1 = (2^(n+3)+1) + 2*(2^(n+2)-1) + 1 = 2^(n+4)
        have hp4 : 2 ^ (n + 2 + 2) = 2 * 2 ^ (n + 3) := by ring
        have hp3 : 2 ^ (n + 3) = 2 * 2 ^ (n + 2) := by ring
        rw [hp4]; nlinarith
      · intro hodd
        rw [totalFibcubeFVector_succ_succ]
        have h0 := ih0_odd (by omega)
        have h1 := ih1_even (by omega); rw [hpow] at h1
        have hp4 : 2 ^ (n + 2 + 2) = 2 * 2 ^ (n + 3) := by ring
        have hp3 : 2 ^ (n + 3) = 2 * 2 ^ (n + 2) := by ring
        rw [hp4]; nlinarith

/-- Closed form for even n: 3·T(n)+1 = 2^{n+2}.
    cor:pom-fibcube-fpoly-growth-constant -/
theorem totalFibcubeFVector_closed_even (n : Nat) (hn : n % 2 = 0) :
    3 * totalFibcubeFVector n + 1 = 2 ^ (n + 2) :=
  (totalFibcubeFVector_closed_aux n).1 hn

/-- Closed form for odd n: 3·T(n) = 2^{n+2}+1.
    cor:pom-fibcube-fpoly-growth-constant -/
theorem totalFibcubeFVector_closed_odd (n : Nat) (hn : n % 2 = 1) :
    3 * totalFibcubeFVector n = 2 ^ (n + 2) + 1 :=
  (totalFibcubeFVector_closed_aux n).2 hn

/-- There exists a stable word with popcount = ⌊(m+1)/2⌋.
    thm:pom-fibcube-eccentricity-closed-form -/
theorem ecc_allFalse_achieved (m : Nat) (hm : 1 ≤ m) :
    ∃ (x : X m), popcount x.1 = (m + 1) / 2 := by
  obtain ⟨S, hS, hcard⟩ := pathIndSet_exists_max m hm
  exact ⟨(xEquivPathIndSet m).invFun ⟨S, hS⟩,
    show (wordSupport ((xEquivPathIndSet m).invFun ⟨S, hS⟩).1).card = (m + 1) / 2 by
      simp only [popcount, xEquivPathIndSet, wordSupport_indSetToWord]; exact hcard⟩

/-- 2*e(n) ≥ n*F(n) for n ≥ 3: linear average degree growth.
    cor:pom-fibcube-edge-closed-form -/
theorem fibcubeEdgeCount_ge_n_fib (n : Nat) (hn : 3 ≤ n) :
    n * Nat.fib n ≤ 2 * fibcubeEdgeCount n := by
  have hclosed := fibcubeEdgeCount_closed n
  -- 10*e(n) = 2*n*F(n+1) + 4*(n+1)*F(n)
  -- Need: 5*n*F(n) ≤ 2*n*F(n+1) + 4*(n+1)*F(n)
  -- i.e. n*(5*F(n) - 2*F(n+1)) ≤ 4*(n+1)*F(n)
  -- F(n+1) = F(n) + F(n-1), so 5*F(n) - 2*F(n+1) = 3*F(n) - 2*F(n-1)
  -- For n ≥ 3: F(n) ≥ F(n-1), so 3*F(n) - 2*F(n-1) ≤ 3*F(n) and n*3*F(n) ≤ 4*(n+1)*F(n)
  -- Actually simpler: need n*F(n) ≤ 2*e(n), i.e. 5*n*F(n) ≤ 10*e(n) = 2*n*F(n+1)+4*(n+1)*F(n)
  -- Since F(n+1) ≥ F(n) and 4*(n+1) ≥ 3*n for n ≥ 3:
  have hfmono : Nat.fib n ≤ Nat.fib (n + 1) := Nat.fib_mono (by omega)
  have hfpos : 0 < Nat.fib n := Nat.fib_pos.mpr (by omega)
  nlinarith

end Omega
