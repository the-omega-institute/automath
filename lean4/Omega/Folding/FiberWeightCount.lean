import Omega.Folding.MaxFiberTwoStep
import Omega.Folding.MomentSum

namespace Omega

-- ══════════════════════════════════════════════════════════════
-- All-false word characterization
-- ══════════════════════════════════════════════════════════════

/-- X.ofNat m 0 is the all-false stable word.
    thm:pom-ofNat-zero-allFalse -/
theorem X.ofNat_zero (m : Nat) :
    X.ofNat m 0 = ⟨fun _ => false, no11_allFalse⟩ := by
  have h : stableValue (⟨fun _ => false, no11_allFalse⟩ : X m) = 0 := stableValue_allFalse
  rw [show (0 : Nat) = stableValue (⟨fun _ => false, no11_allFalse⟩ : X m) from h.symm]
  exact X.ofNat_stableValue _

/-- Words with weight exactly F_{m+2} fold to the all-false stable word.
    thm:pom-Fold-allFalse-weight-fib -/
theorem Fold_eq_allFalse_of_weight_eq_fib (w : Word m)
    (hw : weight w = Nat.fib (m + 2)) :
    Fold w = ⟨fun _ => false, no11_allFalse⟩ := by
  have heq := weight_eq_stableValue_add_hiddenBit w
  rw [hw] at heq
  have hlt := stableValue_lt_fib (Fold w)
  have hle := hiddenBit_le_one w
  have hFpos : 0 < Nat.fib (m + 2) := fib_succ_pos (m + 1)
  have hsv : stableValue (Fold w) = 0 := by
    interval_cases (hiddenBit w) <;> omega
  have hall : stableValue (⟨fun _ => false, no11_allFalse⟩ : X m) = 0 := stableValue_allFalse
  exact X.stableValueFin_injective m (by simp [X.stableValueFin, hsv, hall])

/-- Only the all-false word has weight 0. -/
private theorem eq_allFalse_of_weight_zero {m : Nat} (w : Word m) (hw : weight w = 0) :
    w = fun _ => false := by
  induction m with
  | zero => funext i; exact absurd i.isLt (Nat.not_lt_zero _)
  | succ m ih =>
    have hLast : w ⟨m, Nat.lt_succ_self m⟩ = false := by
      by_contra h
      have htrue : w ⟨m, Nat.lt_succ_self m⟩ = true := by
        cases hb : w ⟨m, Nat.lt_succ_self m⟩ <;> simp_all
      have hpos := weight_pos_of_bit_true htrue
      omega
    funext i
    by_cases hi : i.val < m
    · have htr : weight (truncate w) = 0 := by
        rw [weight] at hw; simp only [hLast, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hw
        exact hw
      have := congr_fun (ih (truncate w) htr) ⟨i.val, hi⟩
      simp [truncate] at this; exact this
    · have : i = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext (Nat.eq_of_lt_succ_of_not_lt i.isLt hi)
      rw [this, hLast]

/-- The fiber of allFalse has size 1 + #{weight = F_{m+2}}.
    thm:pom-fiberMultiplicity-allFalse -/
theorem fiberMultiplicity_allFalse (m : Nat) :
    X.fiberMultiplicity (⟨fun _ => false, no11_allFalse⟩ : X m) =
    1 + (Finset.univ.filter (fun w : Word m => weight w = Nat.fib (m + 2))).card := by
  rw [fiberMultiplicity_eq_weight_congr_count]
  simp only [stableValue_allFalse]
  have hFpos : 0 < Nat.fib (m + 2) := fib_succ_pos (m + 1)
  suffices hsplit : Finset.univ.filter (fun w : Word m => weight w % Nat.fib (m + 2) = 0) =
      Finset.univ.filter (fun w : Word m => weight w = 0) ∪
      Finset.univ.filter (fun w : Word m => weight w = Nat.fib (m + 2)) by
    rw [hsplit]
    have hdisjoint : Disjoint
        (Finset.univ.filter (fun w : Word m => weight w = 0))
        (Finset.univ.filter (fun w : Word m => weight w = Nat.fib (m + 2))) := by
      apply Finset.disjoint_filter.mpr
      intro w _ h1 h2; omega
    rw [Finset.card_union_of_disjoint hdisjoint]
    have hone : (Finset.univ.filter (fun w : Word m => weight w = 0)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨fun _ => false, ?_⟩
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hw; exact eq_allFalse_of_weight_zero w hw
      · intro hw; rw [hw]; exact weight_allFalse
    omega
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro hmod
    have hwlt := X.weight_lt_fib w
    have hbound : weight w < 2 * Nat.fib (m + 2) := by
      have : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
      have : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
      omega
    have : weight w = 0 ∨ weight w = Nat.fib (m + 2) := by
      rcases Nat.eq_zero_or_pos (weight w) with h | h
      · left; exact h
      · right
        obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod
        have hk_pos : 0 < k := by
          rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · rw [hk0, Nat.mul_zero] at hk; omega
          · exact hk0
        have hk_lt : k < 2 := by
          by_contra hge
          push_neg at hge
          have : 2 * Nat.fib (m + 2) ≤ Nat.fib (m + 2) * k := by
            calc 2 * Nat.fib (m + 2) = Nat.fib (m + 2) * 2 := by ring
              _ ≤ Nat.fib (m + 2) * k := Nat.mul_le_mul_left _ hge
          omega
        have : k = 1 := by omega
        rw [this, Nat.mul_one] at hk; omega
    exact this
  · rintro (h | h) <;> simp [h]

-- ══════════════════════════════════════════════════════════════
-- exactWeightCount: counting words of a given weight
-- ══════════════════════════════════════════════════════════════

/-- Number of m-bit words with exactly weight n.
    def:pom-exactWeightCount -/
def exactWeightCount (m n : Nat) : Nat :=
  (Finset.univ.filter (fun w : Word m => weight w = n)).card

/-- thm:pom-ewc-zero-zero -/
theorem exactWeightCount_zero_zero : exactWeightCount 0 0 = 1 := by decide

/-- thm:pom-ewc-zero-succ -/
theorem exactWeightCount_zero_succ (n : Nat) : exactWeightCount 0 (n + 1) = 0 := by
  unfold exactWeightCount
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies,
    weight]; omega

/-- Last-bit split: ewc(m+1, n) = ewc(m, n) + ewc(m, n - F_{m+2}).
    thm:pom-ewc-succ -/
theorem exactWeightCount_succ (m n : Nat) :
    exactWeightCount (m + 1) n =
    exactWeightCount m n +
    (if Nat.fib (m + 2) ≤ n then exactWeightCount m (n - Nat.fib (m + 2)) else 0) := by
  classical
  unfold exactWeightCount
  have hpartition : Finset.univ.filter (fun w : Word (m + 1) => weight w = n) =
      (Finset.univ.filter (fun w : Word (m + 1) => weight w = n ∧ w ⟨m, by omega⟩ = false)) ∪
      (Finset.univ.filter (fun w : Word (m + 1) => weight w = n ∧ w ⟨m, by omega⟩ = true)) := by
    ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hw; cases hb : w ⟨m, by omega⟩ <;> simp [hw]
    · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
  have hdisjoint : Disjoint
      (Finset.univ.filter (fun w : Word (m + 1) => weight w = n ∧ w ⟨m, by omega⟩ = false))
      (Finset.univ.filter (fun w : Word (m + 1) => weight w = n ∧ w ⟨m, by omega⟩ = true)) := by
    apply Finset.disjoint_filter.mpr
    intro w _ ⟨_, hF⟩ ⟨_, hT⟩; rw [hF] at hT; exact Bool.noConfusion hT
  rw [hpartition, Finset.card_union_of_disjoint hdisjoint]
  congr 1
  · apply Finset.card_bij (fun (w : Word (m + 1)) _ => truncate w)
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [weight] at hw; simp only [hw.2, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hw
      exact hw.1
    · intro w₁ hw₁ w₂ hw₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw₁ hw₂
      rw [← X.snoc_truncate_last w₁, ← X.snoc_truncate_last w₂, heq, hw₁.2, hw₂.2]
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact ⟨snoc w false, by simp [weight_snoc, hw], by simp⟩
  · split
    · rename_i hle
      apply Finset.card_bij (fun (w : Word (m + 1)) _ => truncate w)
      · intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rw [weight] at hw; simp only [hw.2, ↓reduceIte] at hw; omega
      · intro w₁ hw₁ w₂ hw₂ heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw₁ hw₂
        rw [← X.snoc_truncate_last w₁, ← X.snoc_truncate_last w₂, heq, hw₁.2, hw₂.2]
      · intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        exact ⟨snoc w true, by constructor <;> simp [weight_snoc, hw]; omega, by simp⟩
    · rename_i hlt; push_neg at hlt
      convert Finset.card_empty
      simp only [Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
      intro w ⟨hwn, hwt⟩
      rw [weight] at hwn; simp only [hwt, ↓reduceIte] at hwn; omega

-- ══════════════════════════════════════════════════════════════
-- Upper bound: no word has weight ≥ F(m+3)
-- ══════════════════════════════════════════════════════════════

/-- thm:pom-ewc-zero-ge-fib -/
theorem exactWeightCount_eq_zero_of_ge_fib (m n : Nat) (hn : Nat.fib (m + 3) ≤ n) :
    exactWeightCount m n = 0 := by
  unfold exactWeightCount
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro w _
  have := X.weight_lt_fib w
  omega

/-- ewc(m, n) = 0 when n is at least F_{m+3} (named alias).
    prop:pom-ewc-vanish-large -/
theorem exactWeightCount_zero_of_large (m n : Nat) (hn : Nat.fib (m + 3) ≤ n) :
    exactWeightCount m n = 0 :=
  exactWeightCount_eq_zero_of_ge_fib m n hn

-- ══════════════════════════════════════════════════════════════
-- Fiber multiplicity = two exactWeightCount terms
-- ══════════════════════════════════════════════════════════════

/-- Fiber multiplicity = ewc at stableValue + ewc at stableValue + F.
    thm:pom-fiberMultiplicity-two-ewc -/
theorem fiberMultiplicity_eq_two_ewc (x : X m) :
    X.fiberMultiplicity x =
    exactWeightCount m (stableValue x) +
    exactWeightCount m (stableValue x + Nat.fib (m + 2)) := by
  rw [fiberMultiplicity_eq_weight_congr_count]
  have hFpos : 0 < Nat.fib (m + 2) := fib_succ_pos (m + 1)
  have hsv_lt := stableValue_lt_fib x
  suffices hsplit : Finset.univ.filter (fun w : Word m => weight w % Nat.fib (m + 2) = stableValue x)
      = Finset.univ.filter (fun w : Word m => weight w = stableValue x) ∪
        Finset.univ.filter (fun w : Word m => weight w = stableValue x + Nat.fib (m + 2)) by
    rw [hsplit]
    have hdisjoint : Disjoint
        (Finset.univ.filter (fun w : Word m => weight w = stableValue x))
        (Finset.univ.filter (fun w : Word m => weight w = stableValue x + Nat.fib (m + 2))) := by
      apply Finset.disjoint_filter.mpr; intro w _ h1 h2; omega
    rw [Finset.card_union_of_disjoint hdisjoint]; rfl
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro hmod
    have hwlt := X.weight_lt_fib w
    have hbound : weight w < 2 * Nat.fib (m + 2) := by
      have : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
      have : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
      omega
    have hdiv := Nat.div_add_mod (weight w) (Nat.fib (m + 2))
    rw [hmod] at hdiv
    have hq_lt : weight w / Nat.fib (m + 2) < 2 := Nat.div_lt_of_lt_mul (by omega)
    interval_cases (weight w / Nat.fib (m + 2))
    · left; omega
    · right; omega
  · rintro (h | h)
    · rw [h]; exact Nat.mod_eq_of_lt hsv_lt
    · rw [h, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hsv_lt

-- ══════════════════════════════════════════════════════════════
-- Double-step split for exactWeightCount
-- ══════════════════════════════════════════════════════════════

/-- thm:pom-ewc-succ-succ -/
theorem exactWeightCount_succ_succ (m n : Nat) :
    exactWeightCount (m + 2) n =
    exactWeightCount m n +
    (if Nat.fib (m + 2) ≤ n then exactWeightCount m (n - Nat.fib (m + 2)) else 0) +
    (if Nat.fib (m + 3) ≤ n then exactWeightCount m (n - Nat.fib (m + 3)) else 0) +
    (if Nat.fib (m + 4) ≤ n then exactWeightCount m (n - Nat.fib (m + 4)) else 0) := by
  have hfib4 : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := by
    have := Nat.fib_add_two (n := m + 2); omega
  -- ewc(m+2, n) = ewc(m+1, n) + if F3 ≤ n then ewc(m+1, n-F3) else 0
  have step1 : exactWeightCount (m + 2) n =
      exactWeightCount (m + 1) n +
      (if Nat.fib (m + 3) ≤ n then exactWeightCount (m + 1) (n - Nat.fib (m + 3)) else 0) := by
    have := exactWeightCount_succ (m + 1) n
    rwa [show Nat.fib (m + 1 + 2) = Nat.fib (m + 3) from by ring_nf] at this
  -- ewc(m+1, n) = ewc(m,n) + if F2 ≤ n then ewc(m, n-F2) else 0
  have step2 := exactWeightCount_succ m n
  -- ewc(m+1, n-F3) = ewc(m, n-F3) + if F2 ≤ n-F3 then ewc(m, n-F3-F2) else 0
  rw [step1, step2]
  by_cases h3 : Nat.fib (m + 3) ≤ n
  · simp only [if_pos h3]
    have step3 := exactWeightCount_succ m (n - Nat.fib (m + 3))
    rw [step3]
    by_cases h4 : Nat.fib (m + 4) ≤ n
    · have h23 : Nat.fib (m + 2) ≤ n - Nat.fib (m + 3) := by omega
      simp only [ if_pos h4, if_pos h23]
      rw [show n - Nat.fib (m + 3) - Nat.fib (m + 2) = n - Nat.fib (m + 4) from by omega]
      ring
    · have h23 : ¬ (Nat.fib (m + 2) ≤ n - Nat.fib (m + 3)) := by omega
      simp only [if_neg h4, if_neg h23]; ring
  · have h4 : ¬ (Nat.fib (m + 4) ≤ n) := by omega
    simp only [if_neg h3, if_neg h4]

-- ══════════════════════════════════════════════════════════════
-- Fibonacci parameter specialization
-- ══════════════════════════════════════════════════════════════

private theorem exactWeightCount_zero_eq_one (m : Nat) : exactWeightCount m 0 = 1 := by
  unfold exactWeightCount
  rw [Finset.card_eq_one]
  refine ⟨fun _ => false, ?_⟩
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun hw => eq_allFalse_of_weight_zero w hw, fun hw => by rw [hw]; exact weight_allFalse⟩

/-- thm:pom-ewc-fib-shift -/
theorem exactWeightCount_fib_shift (m : Nat) :
    exactWeightCount (m + 2) (Nat.fib (m + 4)) = exactWeightCount m (Nat.fib (m + 2)) + 1 := by
  have hfib4 : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := by
    have := Nat.fib_add_two (n := m + 2); omega
  -- Compute each term directly
  have t1 : exactWeightCount m (Nat.fib (m + 4)) = 0 :=
    exactWeightCount_eq_zero_of_ge_fib m _ (by omega)
  have t2 : exactWeightCount m (Nat.fib (m + 4) - Nat.fib (m + 2)) = 0 := by
    rw [show Nat.fib (m + 4) - Nat.fib (m + 2) = Nat.fib (m + 3) from by omega]
    exact exactWeightCount_eq_zero_of_ge_fib m _ (le_refl _)
  have t3 : exactWeightCount m (Nat.fib (m + 4) - Nat.fib (m + 3)) =
      exactWeightCount m (Nat.fib (m + 2)) := by
    congr 1; omega
  have t4 : exactWeightCount m (Nat.fib (m + 4) - Nat.fib (m + 4)) = 1 := by
    rw [Nat.sub_self]; exact exactWeightCount_zero_eq_one m
  rw [exactWeightCount_succ_succ,
    if_pos (show Nat.fib (m + 2) ≤ Nat.fib (m + 4) from by omega),
    if_pos (show Nat.fib (m + 3) ≤ Nat.fib (m + 4) from Nat.fib_mono (by omega)),
    if_pos (show Nat.fib (m + 4) ≤ Nat.fib (m + 4) from le_refl _),
    t1, t2, t3, t4]; omega

-- ══════════════════════════════════════════════════════════════
-- allFalse fiber recurrence
-- ══════════════════════════════════════════════════════════════

/-- thm:pom-fM-allFalse-recurrence -/
theorem fiberMultiplicity_allFalse_recurrence (m : Nat) :
    X.fiberMultiplicity (⟨fun _ => false, no11_allFalse⟩ : X (m + 2)) =
    X.fiberMultiplicity (⟨fun _ => false, no11_allFalse⟩ : X m) + 1 := by
  -- fM(allFalse, m+2) = 1 + #{weight = F((m+2)+2)} = 1 + ewc(m+2, F(m+4))
  have h1 := fiberMultiplicity_allFalse (m + 2)
  rw [show (m + 2) + 2 = m + 4 from by omega] at h1
  -- ewc(m+2, F(m+4)) = ewc(m, F(m+2)) + 1
  have h2 := exactWeightCount_fib_shift m
  -- fM(allFalse, m) = 1 + #{weight = F(m+2)} = 1 + ewc(m, F(m+2))
  have h3 := fiberMultiplicity_allFalse m
  -- Combine: fM(m+2) = 1 + (ewc(m,F2)+1) = (1+ewc(m,F2)) + 1 = fM(m) + 1
  rw [h1]; unfold exactWeightCount at h2; rw [h2, h3]; ring

-- ══════════════════════════════════════════════════════════════
-- allFalse fiber closed form
-- ══════════════════════════════════════════════════════════════

/-- thm:pom-fM-allFalse-closed -/
theorem fiberMultiplicity_allFalse_closed (m : Nat) :
    X.fiberMultiplicity (⟨fun _ => false, no11_allFalse⟩ : X m) = m / 2 + 1 := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 =>
      -- fM(allFalse, 0) = ewc(0,0) + ewc(0,F2) = 1 + 0 = 1
      rw [fiberMultiplicity_eq_two_ewc, stableValue_allFalse]
      simp only [Nat.zero_add, show Nat.fib 2 = 1 from by simp [Nat.fib]]
      rw [exactWeightCount_zero_eq_one, exactWeightCount_zero_succ]
    | 1 =>
      -- fM(allFalse, 1) = ewc(1,0) + ewc(1,F3) = 1 + 0 = 1
      rw [fiberMultiplicity_eq_two_ewc, stableValue_allFalse]
      simp only [Nat.zero_add]
      rw [exactWeightCount_zero_eq_one]
      -- Need: ewc(1, Nat.fib 3) = 0
      -- Nat.fib 3 = 2, ewc(1, 2) = ewc(0, 2) + (if 1 ≤ 2 then ewc(0, 1) else 0) = 0 + 0 = 0
      have : exactWeightCount 1 (Nat.fib 3) = 0 := by
        rw [exactWeightCount_succ]
        simp only [show Nat.fib (0 + 2) = 1 from by simp [Nat.fib],
          show Nat.fib 3 = 2 from by simp [Nat.fib]]
        simp [exactWeightCount_zero_succ]
      rw [this]
    | m + 2 =>
      rw [fiberMultiplicity_allFalse_recurrence, ih m (by omega)]
      -- Goal: m / 2 + 1 + 1 = (m + 2) / 2 + 1
      -- (m + 2) / 2 = m / 2 + 1 for natural number division
      omega

/-- Exact weight count at weight F_{m+2} equals ⌊m/2⌋.
    prop:pom-ewc-fib-closed -/
theorem exactWeightCount_fib_closed (m : Nat) :
    exactWeightCount m (Nat.fib (m + 2)) = m / 2 := by
  have h1 := fiberMultiplicity_allFalse m
  have h2 := fiberMultiplicity_allFalse_closed m
  unfold exactWeightCount
  omega

-- ══════════════════════════════════════════════════════════════
-- Weight congruence class count
-- ══════════════════════════════════════════════════════════════

/-- Weight congruence class count: #{w : Word m | weight w % F_{m+2} = r}.
    def:pom-wcc -/
def weightCongruenceCount (m r : Nat) : Nat :=
  (Finset.univ.filter (fun w : Word m => weight w % Nat.fib (m + 2) = r)).card

/-- wcc = ewc(r) + ewc(r + F).
    thm:pom-wcc-eq-sum-ewc -/
theorem weightCongruenceCount_eq_sum_ewc (m r : Nat) (hr : r < Nat.fib (m + 2)) :
    weightCongruenceCount m r =
    exactWeightCount m r + exactWeightCount m (r + Nat.fib (m + 2)) := by
  unfold weightCongruenceCount exactWeightCount
  -- Same pattern as fiberMultiplicity_eq_two_ewc
  have hFpos : 0 < Nat.fib (m + 2) := fib_succ_pos (m + 1)
  suffices hsplit : Finset.univ.filter (fun w : Word m => weight w % Nat.fib (m + 2) = r)
      = Finset.univ.filter (fun w : Word m => weight w = r) ∪
        Finset.univ.filter (fun w : Word m => weight w = r + Nat.fib (m + 2)) by
    rw [hsplit]
    exact Finset.card_union_of_disjoint
      (Finset.disjoint_filter.mpr fun w _ h1 h2 => by omega)
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro hmod
    have hwlt := X.weight_lt_fib w
    have hbound : weight w < 2 * Nat.fib (m + 2) := by
      have : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
      have : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
      omega
    have hdiv := Nat.div_add_mod (weight w) (Nat.fib (m + 2))
    rw [hmod] at hdiv
    have hq_lt : weight w / Nat.fib (m + 2) < 2 := Nat.div_lt_of_lt_mul (by omega)
    interval_cases (weight w / Nat.fib (m + 2))
    · left; omega
    · right; omega
  · rintro (h | h)
    · rw [h]; exact Nat.mod_eq_of_lt hr
    · rw [h, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hr

/-- d(x) = wcc(m, stableValue x).
    thm:pom-fiberMultiplicity-eq-wcc -/
theorem fiberMultiplicity_eq_wcc (x : X m) :
    X.fiberMultiplicity x = weightCongruenceCount m (stableValue x) := by
  rw [fiberMultiplicity_eq_weight_congr_count]; rfl

-- ══════════════════════════════════════════════════════════════
-- S_2 = sum of squared congruence class sizes
-- ══════════════════════════════════════════════════════════════

/-- S_2(m) = sum of squared congruence class sizes.
    prop:pom-moment-congruence-q -/
theorem momentSum_two_eq_congr_sq_sum (m : Nat) :
    momentSum 2 m =
    ∑ r ∈ Finset.range (Nat.fib (m + 2)), weightCongruenceCount m r ^ 2 := by
  unfold momentSum
  -- Step 1: rewrite fiberMultiplicity as wcc
  simp_rw [fiberMultiplicity_eq_wcc]
  -- Step 2: reparametrize via stableValueFin bijection
  -- ∑ x : X m, wcc(m, stableValue x)^2 = ∑ r : Fin F, wcc(m, r.val)^2
  have hbij := X.stableValueFin_bijective m
  have step : ∑ x : X m, weightCongruenceCount m (stableValue x) ^ 2 =
      ∑ r : Fin (Nat.fib (m + 2)), weightCongruenceCount m r.val ^ 2 := by
    rw [show (fun x : X m => weightCongruenceCount m (stableValue x) ^ 2) =
      (fun r : Fin (Nat.fib (m + 2)) => weightCongruenceCount m r.val ^ 2) ∘
      X.stableValueFin from by ext x; simp [X.stableValueFin]]
    exact hbij.sum_comp (fun r : Fin (Nat.fib (m + 2)) => weightCongruenceCount m r.val ^ 2)
  rw [step, ← Fin.sum_univ_eq_sum_range]


-- ══════════════════════════════════════════════════════════════
-- Snoc embedding: ewc(m,n) ≤ d_{m+1}(ofNat(m+1,n))
-- ══════════════════════════════════════════════════════════════

/-- snoc false embeds the exact-weight-n subfiber: d_{m+1}(ofNat(m+1,n)) ≥ ewc(m,n). -/
theorem fiberMultiplicity_ge_ewc_via_snoc (m n : Nat) (_hn : n < Nat.fib (m + 3)) :
    X.fiberMultiplicity (X.ofNat (m + 1) n) ≥ exactWeightCount m n := by
  classical
  let y := X.ofNat (m + 1) n
  show (X.fiber y).card ≥ (Finset.univ.filter (fun w : Word m => weight w = n)).card
  apply Finset.card_le_card_of_injOn (fun w => snoc w false)
    (fun w hw => by
      have hwn : weight w = n := by simpa using hw
      show snoc w false ∈ X.fiber y
      rw [X.mem_fiber]
      rw [Fold_snoc_false_eq, hwn])
    (fun w₁ _ w₂ _ h => by
      have := congr_arg truncate h; simp at this; exact this)

/-- Σ ewc(m,n) = 2^m: exact weight counts partition the word space.
    prop:pom-moment-congruence-q -/
theorem exactWeightCount_sum (m : Nat) :
    ∑ n ∈ Finset.range (Nat.fib (m + 3)), exactWeightCount m n = 2 ^ m := by
  -- Σ ewc(n) = Σ |{w : weight w = n}| = |Word m| = 2^m
  unfold exactWeightCount
  rw [← Finset.card_biUnion]
  · -- The union of all weight-n subsets = all words
    conv_rhs => rw [show 2 ^ m = Fintype.card (Word m) from by simp [Fintype.card_fin]]
    rw [← Finset.card_univ]
    congr 1; ext w; simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨fun ⟨_, _, h⟩ => True.intro, fun _ => ⟨weight w, X.weight_lt_fib w, rfl⟩⟩
  · intro n _ n' _ hne
    apply Finset.disjoint_filter.mpr
    intro w _ h1 h2; exact hne (h1.symm.trans h2)

/-- For n < F_{m+2}, ewc(m+1,n) = ewc(m,n): no contribution from the last bit.
    bridge:ewc-level-stability -/
theorem exactWeightCount_succ_of_lt (m n : Nat) (hn : n < Nat.fib (m + 2)) :
    exactWeightCount (m + 1) n = exactWeightCount m n := by
  rw [exactWeightCount_succ]; simp [show ¬(Nat.fib (m + 2) ≤ n) from by omega]

-- ══════════════════════════════════════════════════════════════
-- Phase 147: sum over words grouped by weight
-- ══════════════════════════════════════════════════════════════

/-- Sum over words grouped by weight: Σ_w f(weight w) = Σ_n ewc(m,n) · f(n).
    bridge:weight-fiber-counting -/
theorem sum_word_apply_weight (f : Nat → Nat) :
    ∑ w : Word m, f (weight w) =
    ∑ n ∈ Finset.range (Nat.fib (m + 3)), exactWeightCount m n * f n := by
  classical
  let wsets := fun n => Finset.univ.filter (fun w : Word m => weight w = n)
  have hDisjoint : (↑(Finset.range (Nat.fib (m + 3))) : Set Nat).PairwiseDisjoint wsets := by
    intro n _ n' _ hne
    exact Finset.disjoint_filter.mpr (fun w _ h1 h2 => hne (h1.symm.trans h2))
  have hUnion : (Finset.univ : Finset (Word m)) =
      (Finset.range (Nat.fib (m + 3))).biUnion wsets := by
    ext w; simp only [wsets, Finset.mem_univ, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_filter, true_and, true_iff]
    exact ⟨weight w, X.weight_lt_fib w, rfl⟩
  change Finset.univ.sum (fun w => f (weight w)) = _
  rw [hUnion, Finset.sum_biUnion hDisjoint]
  apply Finset.sum_congr rfl; intro n _
  have : ∀ w ∈ wsets n, f (weight w) = f n :=
    fun w hw => by rw [(Finset.mem_filter.mp hw).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, exactWeightCount]

-- ══════════════════════════════════════════════════════════════
-- Phase 224: exactWeightCount upper bound
-- ══════════════════════════════════════════════════════════════

private theorem exactWeightCount_zero_le_one (n : Nat) : exactWeightCount 0 n ≤ 1 := by
  rcases n with _ | n
  · rw [exactWeightCount_zero_zero]
  · rw [exactWeightCount_zero_succ]; omega

/-- Helper: ewc(m+1, n) ≤ 2^m for all n. -/
private theorem exactWeightCount_succ_le (m n : Nat) :
    exactWeightCount (m + 1) n ≤ 2 ^ m := by
  induction m generalizing n with
  | zero =>
    -- ewc(1, n) = ewc(0,n) + (if 1≤n then ewc(0,n-1) else 0); case split on n
    rw [exactWeightCount_succ]
    simp only [show Nat.fib (0 + 2) = 1 from by simp [Nat.fib]]
    rcases n with _ | _ | n
    · simp [exactWeightCount_zero_zero]
    · simp [exactWeightCount_zero_succ, exactWeightCount_zero_zero]
    · simp [exactWeightCount_zero_succ]
  | succ m ih =>
    rw [exactWeightCount_succ]
    have h1 := ih n
    have hpow : 2 ^ m + 2 ^ m = 2 ^ (m + 1) := by ring
    split
    · have h2 := ih (n - Nat.fib (m + 1 + 2)); linarith
    · linarith

/-- Each weight class has at most 2^(m-1) words.
    prop:pom-ewc-upper-bound -/
theorem exactWeightCount_le_pow (m n : Nat) (hm : 1 ≤ m) :
    exactWeightCount m n ≤ 2 ^ (m - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  exact exactWeightCount_succ_le m n

-- ══════════════════════════════════════════════════════════════
-- Phase 224: pigeonhole on maxFiberMultiplicity
-- ══════════════════════════════════════════════════════════════

/-- Σ d(x) = 2^m (wrapper with paper tag). prop:pom-fold-partition -/
theorem fiberMultiplicity_sum_eq_pow' (m : Nat) :
    ∑ x : X m, X.fiberMultiplicity x = 2 ^ m :=
  X.fiberMultiplicity_sum_eq_pow m

/-- 2^m ≤ D(m) * F(m+2) (pigeonhole). cor:pom-D-le-avg -/
theorem pow_le_maxFiberMultiplicity_mul_fib (m : Nat) :
    2 ^ m ≤ X.maxFiberMultiplicity m * Nat.fib (m + 2) := by
  calc 2 ^ m = ∑ x : X m, X.fiberMultiplicity x := (X.fiberMultiplicity_sum_eq_pow m).symm
    _ ≤ ∑ _ : X m, X.maxFiberMultiplicity m :=
        Finset.sum_le_sum (fun x _ => X.fiberMultiplicity_le_max x)
    _ = Fintype.card (X m) * X.maxFiberMultiplicity m := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
    _ = X.maxFiberMultiplicity m * Fintype.card (X m) := Nat.mul_comm _ _
    _ = X.maxFiberMultiplicity m * Nat.fib (m + 2) := by
        rw [X.card_eq_fib]

-- ══════════════════════════════════════════════════════════════
-- Phase 227: weightCongruenceCount positivity
-- ══════════════════════════════════════════════════════════════

/-- wcc(m,r) > 0 for r < F(m+2). prop:pom-moment-congruence-q -/
theorem weightCongruenceCount_pos (m : Nat) (r : Nat) (hr : r < Nat.fib (m + 2)) :
    0 < weightCongruenceCount m r := by
  -- wcc(m, r) = fiberMultiplicity(ofNat m r) which is always positive
  rw [show r = stableValue (X.ofNat m r) from (X.stableValue_ofNat_lt r hr).symm,
    ← fiberMultiplicity_eq_wcc]
  exact X.fiberMultiplicity_pos _

-- ══════════════════════════════════════════════════════════════
-- Phase R3: fiberHiddenBitCount and branch mass law
-- ══════════════════════════════════════════════════════════════

/-- Count of words in fiber(x) with hiddenBit = b.
    cor:pom-branch-mass-law -/
noncomputable def fiberHiddenBitCount (b : Nat) (x : X m) : Nat :=
  (X.fiber x).filter (fun w => hiddenBit w = b) |>.card

/-- Fiber multiplicity splits by hidden bit: d(x) = d_0(x) + d_1(x).
    cor:pom-branch-mass-law -/
theorem fiberMultiplicity_split_by_hiddenBit (x : X m) :
    X.fiberMultiplicity x = fiberHiddenBitCount 0 x + fiberHiddenBitCount 1 x := by
  classical
  simp only [X.fiberMultiplicity, fiberHiddenBitCount]
  -- Split fiber(x) by hiddenBit = 0 vs hiddenBit = 1
  -- fiber(x) = {b=0} ∪ {b=1}, disjoint
  have h0 : ((X.fiber x).filter (fun w => hiddenBit w = 0)).card +
      ((X.fiber x).filter (fun w => ¬hiddenBit w = 0)).card = (X.fiber x).card :=
    Finset.card_filter_add_card_filter_not (s := X.fiber x) (fun w => hiddenBit w = 0)
  have hconv : (X.fiber x).filter (fun w => ¬hiddenBit w = 0) =
      (X.fiber x).filter (fun w => hiddenBit w = 1) := by
    congr 1; ext w; have := hiddenBit_le_one w; omega
  rw [hconv] at h0; omega

/-- Sum of d_{m,1}(x) over all x = hiddenBitCount m.
    cor:pom-branch-mass-law -/
theorem fiberHiddenBitCount_one_sum (m : Nat) :
    ∑ x : X m, fiberHiddenBitCount 1 x = hiddenBitCount m := by
  classical
  simp only [fiberHiddenBitCount, hiddenBitCount]
  -- ∑_x |fiber(x) ∩ {b=1}| = |{w | b(w)=1}| via fiber partition
  -- LHS = ∑_x |fiber(x).filter (hiddenBit = 1)|
  -- RHS = |univ.filter (weight ≥ F_{m+2})|
  -- First, rewrite hiddenBit = 1 as weight ≥ F_{m+2}
  have hpred : ∀ w : Word m, hiddenBit w = 1 ↔ Nat.fib (m + 2) ≤ weight w := by
    intro w; unfold hiddenBit; split <;> omega
  -- Now exchange sum of card-filters over fibers with a single filter
  have hDisjoint : (↑(Finset.univ : Finset (X m)) : Set (X m)).PairwiseDisjoint X.fiber := by
    intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro w hwx hwy
    exact hxy ((X.mem_fiber.1 hwx).symm.trans (X.mem_fiber.1 hwy))
  have hUnion : (Finset.univ : Finset (Word m)) = Finset.univ.biUnion X.fiber := by
    ext w; simp only [Finset.mem_univ, Finset.mem_biUnion, true_iff]
    exact ⟨Fold w, trivial, X.mem_fiber_Fold w⟩
  -- ∑_x |fiber(x).filter p| = |univ.filter p| for any predicate p
  conv_rhs => rw [hUnion]
  rw [Finset.filter_biUnion]
  rw [Finset.card_biUnion (by
    intro x _ y _ hxy
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]
    intro w hwx hwy
    exact hxy ((X.mem_fiber.1 hwx).symm.trans (X.mem_fiber.1 hwy)))]
  congr 1; ext x
  congr 1; ext w
  simp only [Finset.mem_filter, hpred]

/-- Sum of d_{m,0}(x) over all x = 2^m - hiddenBitCount m.
    cor:pom-branch-mass-law -/
theorem fiberHiddenBitCount_zero_sum (m : Nat) :
    ∑ x : X m, fiberHiddenBitCount 0 x = 2 ^ m - hiddenBitCount m := by
  have hsplit : ∀ x : X m, X.fiberMultiplicity x =
      fiberHiddenBitCount 0 x + fiberHiddenBitCount 1 x :=
    fiberMultiplicity_split_by_hiddenBit
  have hsum : ∑ x : X m, X.fiberMultiplicity x = 2 ^ m := X.fiberMultiplicity_sum_eq_pow m
  have h1 : ∑ x : X m, fiberHiddenBitCount 1 x = hiddenBitCount m :=
    fiberHiddenBitCount_one_sum m
  have h01 : ∑ x : X m, X.fiberMultiplicity x =
      ∑ x : X m, fiberHiddenBitCount 0 x + ∑ x : X m, fiberHiddenBitCount 1 x := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun x _ => hsplit x)
  -- hiddenBitCount m ≤ 2^m (since it counts a subset of 2^m words)
  have hle : hiddenBitCount m ≤ 2 ^ m := by
    rw [← hsum, ← h1]; exact Finset.sum_le_sum (fun x _ => by
      rw [hsplit x]; omega)
  omega

/-- Paper-facing package for `cor:pom-branch-mass-law`. -/
theorem paper_pom_branch_mass_law (m : Nat) :
    (∀ x : X m, X.fiberMultiplicity x = fiberHiddenBitCount 0 x + fiberHiddenBitCount 1 x) ∧
    (∑ x : X m, fiberHiddenBitCount 1 x = hiddenBitCount m) ∧
    (∑ x : X m, fiberHiddenBitCount 0 x = 2 ^ m - hiddenBitCount m) := by
  exact ⟨fiberMultiplicity_split_by_hiddenBit, fiberHiddenBitCount_one_sum m,
    fiberHiddenBitCount_zero_sum m⟩

-- ══════════════════════════════════════════════════════════════
-- ══════════════════════════════════════════════════════════════
-- Phase R6: hidden-bit ↔ ewc bridges
-- ══════════════════════════════════════════════════════════════

/-- d_{m,0}(x) = ewc(m, stableValue(x)).
    cor:pom-branch-mass-law (hidden-bit ↔ ewc bridge) -/
theorem fiberHiddenBitCount_zero_eq_ewc (x : X m) :
    fiberHiddenBitCount 0 x = exactWeightCount m (stableValue x) := by
  simp only [fiberHiddenBitCount, exactWeightCount]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, X.mem_fiber]
  constructor
  · -- Fold w = x ∧ hiddenBit w = 0 → weight w = stableValue x
    rintro ⟨hfold, hhid⟩
    have heq := weight_eq_stableValue_add_hiddenBit w
    rw [hfold, hhid] at heq; omega
  · -- weight w = stableValue x → Fold w = x ∧ hiddenBit w = 0
    intro hw
    have hsv_lt := stableValue_lt_fib x
    constructor
    · have hmod : weight w % Nat.fib (m + 2) = stableValue x := by
        rw [hw, Nat.mod_eq_of_lt hsv_lt]
      exact X.mem_fiber.mp ((mem_fiber_iff_weight_mod x w).mpr hmod)
    · unfold hiddenBit; simp only [show ¬(Nat.fib (m + 2) ≤ weight w) from by omega, ite_false]

/-- d_{m,1}(x) = ewc(m, stableValue(x) + F_{m+2}).
    cor:pom-branch-mass-law (hidden-bit ↔ ewc bridge) -/
theorem fiberHiddenBitCount_one_eq_ewc (x : X m) :
    fiberHiddenBitCount 1 x = exactWeightCount m (stableValue x + Nat.fib (m + 2)) := by
  simp only [fiberHiddenBitCount, exactWeightCount]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, X.mem_fiber]
  constructor
  · -- Fold w = x ∧ hiddenBit w = 1 → weight w = stableValue x + F_{m+2}
    rintro ⟨hfold, hhid⟩
    have heq := weight_eq_stableValue_add_hiddenBit w
    rw [hfold, hhid] at heq; omega
  · -- weight w = stableValue x + F_{m+2} → Fold w = x ∧ hiddenBit w = 1
    intro hw
    have hsv_lt := stableValue_lt_fib x
    constructor
    · have hmod : weight w % Nat.fib (m + 2) = stableValue x := by
        rw [hw, Nat.add_mod_right, Nat.mod_eq_of_lt hsv_lt]
      exact X.mem_fiber.mp ((mem_fiber_iff_weight_mod x w).mpr hmod)
    · unfold hiddenBit; simp only [show Nat.fib (m + 2) ≤ weight w from by omega, ite_true]

-- Phase R10 theorem 2: d_0 ≥ d_1 via ewc shift monotonicity — deferred (complex recursion)
-- Phase R5: hiddenBit sum, weight decomp, S2 expand
-- ══════════════════════════════════════════════════════════════

/-- Sum of hiddenBit indicator equals hiddenBitCount.
    cor:pom-branch-mass-law -/
theorem hiddenBit_sum_eq_hiddenBitCount (m : Nat) :
    ∑ w : Word m, hiddenBit w = hiddenBitCount m := by
  simp only [hiddenBit, hiddenBitCount, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Weight total sum = Σ d(x)·sv(x) + hiddenBitCount(m)·F_{m+2}.
    lem:pom-one-bit -/
theorem weight_sum_fiber_decomp (m : Nat) :
    ∑ w : Word m, weight w =
    ∑ x : X m, X.fiberMultiplicity x * stableValue x +
    hiddenBitCount m * Nat.fib (m + 2) := by
  -- Step 1: weight = stableValue(Fold w) + hiddenBit(w) * F
  conv_lhs => arg 2; ext w; rw [weight_eq_stableValue_add_hiddenBit w]
  rw [Finset.sum_add_distrib]
  congr 1
  · -- ∑ stableValue(Fold w) = ∑ d(x) * sv(x) via fiber partition
    classical
    have hDisjoint : (↑(Finset.univ : Finset (X m)) : Set (X m)).PairwiseDisjoint X.fiber := by
      intro x _ y _ hxy; rw [Function.onFun, Finset.disjoint_left]
      intro w hwx hwy; exact hxy ((X.mem_fiber.1 hwx).symm.trans (X.mem_fiber.1 hwy))
    have hUnion : (Finset.univ : Finset (Word m)) = Finset.univ.biUnion X.fiber := by
      ext w; simp only [Finset.mem_univ, Finset.mem_biUnion, true_iff]
      exact ⟨Fold w, trivial, X.mem_fiber_Fold w⟩
    change Finset.univ.sum (fun w => stableValue (Fold w)) = _
    rw [hUnion, Finset.sum_biUnion hDisjoint]
    apply Finset.sum_congr rfl; intro x _
    have : ∀ w ∈ X.fiber x, stableValue (Fold w) = stableValue x :=
      fun w hw => by rw [X.mem_fiber.1 hw]
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, X.fiberMultiplicity]
  · -- ∑ hiddenBit(w) * F = hiddenBitCount(m) * F
    rw [← Finset.sum_mul, hiddenBit_sum_eq_hiddenBitCount]

/-- S_2(m) = Σ d_0² + 2·Σ d_0·d_1 + Σ d_1² (hidden-bit expansion).
    prop:pom-hiddenbit-mixed-moment-cluster -/
theorem momentSum_two_hiddenBit_expand (m : Nat) :
    momentSum 2 m =
    ∑ x : X m, fiberHiddenBitCount 0 x ^ 2 +
    2 * ∑ x : X m, fiberHiddenBitCount 0 x * fiberHiddenBitCount 1 x +
    ∑ x : X m, fiberHiddenBitCount 1 x ^ 2 := by
  simp only [momentSum]
  -- d(x)^2 = (d_0(x) + d_1(x))^2 = d_0^2 + 2*d_0*d_1 + d_1^2
  have hsplit : ∀ x : X m, X.fiberMultiplicity x ^ 2 =
      fiberHiddenBitCount 0 x ^ 2 +
      2 * (fiberHiddenBitCount 0 x * fiberHiddenBitCount 1 x) +
      fiberHiddenBitCount 1 x ^ 2 := by
    intro x
    rw [fiberMultiplicity_split_by_hiddenBit x]
    ring
  simp_rw [hsplit, Finset.sum_add_distrib, Finset.mul_sum]

/-- General hidden-bit mixed-moment cluster expansion.
    prop:pom-hiddenbit-mixed-moment-cluster -/
theorem paper_pom_hiddenbit_mixed_moment_cluster (k m : Nat) :
    momentSum k m = Finset.sum (Finset.range (k + 1)) (fun a =>
      Nat.choose k a * ∑ x : X m, fiberHiddenBitCount 0 x ^ a * fiberHiddenBitCount 1 x ^ (k - a)) := by
  classical
  rw [momentSum]
  calc
    ∑ x : X m, X.fiberMultiplicity x ^ k
      = ∑ x : X m, (fiberHiddenBitCount 0 x + fiberHiddenBitCount 1 x) ^ k := by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [fiberMultiplicity_split_by_hiddenBit x]
    _ = ∑ x : X m, Finset.sum (Finset.range (k + 1)) (fun a =>
          Nat.choose k a * (fiberHiddenBitCount 0 x ^ a * fiberHiddenBitCount 1 x ^ (k - a))) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            add_pow (fiberHiddenBitCount 0 x) (fiberHiddenBitCount 1 x) k
    _ = Finset.sum (Finset.range (k + 1)) (fun a => ∑ x : X m,
          Nat.choose k a * (fiberHiddenBitCount 0 x ^ a * fiberHiddenBitCount 1 x ^ (k - a))) := by
          rw [Finset.sum_comm]
    _ = Finset.sum (Finset.range (k + 1)) (fun a =>
          Nat.choose k a * ∑ x : X m, fiberHiddenBitCount 0 x ^ a * fiberHiddenBitCount 1 x ^ (k - a)) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          simpa using
            (Finset.mul_sum (s := Finset.univ)
              (f := fun x : X m => fiberHiddenBitCount 0 x ^ a * fiberHiddenBitCount 1 x ^ (k - a))
              (a := Nat.choose k a)).symm

/-- Fiber multiplicity equals the sum of two exact weight counts.
    d(x) = ewc(m, sv(x)) + ewc(m, sv(x) + F_{m+2}).
    thm:pom-fiber-ewc-sum -/
theorem fiberMultiplicity_eq_ewc_sum (x : X m) :
    X.fiberMultiplicity x =
    exactWeightCount m (stableValue x) +
    exactWeightCount m (stableValue x + Nat.fib (m + 2)) := by
  rw [fiberMultiplicity_split_by_hiddenBit x,
    fiberHiddenBitCount_zero_eq_ewc x, fiberHiddenBitCount_one_eq_ewc x]

/-- The sum of exactWeightCount over all possible weights equals 2^m (total word count).
    def:pom-exactWeightCount -/
theorem exactWeightCount_sum_eq_pow (m : Nat) :
    ∑ n ∈ Finset.range (Nat.fib (m + 3)), exactWeightCount m n = 2 ^ m := by
  simp only [exactWeightCount]
  have hmap : Set.MapsTo (fun w : Word m => weight w)
      (↑(Finset.univ : Finset (Word m)) : Set (Word m))
      (↑(Finset.range (Nat.fib (m + 3))) : Set Nat) :=
    fun w _ => Finset.mem_range.mpr (X.weight_lt_fib w)
  rw [← Finset.card_eq_sum_card_fiberwise hmap, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- ewc(m, 1) = 1 for m ≥ 1: exactly one word of weight 1 at each resolution.
    bridge:ewc-weight-one -/
theorem exactWeightCount_one_eq (m : Nat) (hm : 1 ≤ m) :
    exactWeightCount m 1 = 1 := by
  induction m with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => native_decide
    | succ j =>
      rw [exactWeightCount_succ_of_lt (j + 1) 1 (by
        calc 1 < 2 := by omega
          _ = Nat.fib 3 := by native_decide
          _ ≤ Nat.fib (j + 1 + 2) := Nat.fib_mono (by omega))]
      exact ih (by omega)

/-- Weight distribution audit: total = 2^m, recurrence, boundary values.
    prop:fold-groupoid-wedderburn -/
theorem paper_pom_weight_distribution :
    (∀ m : Nat, ∑ n ∈ Finset.range (Nat.fib (m + 3)), exactWeightCount m n = 2 ^ m) ∧
    (∀ m : Nat, exactWeightCount m 0 = 1) ∧
    (∀ m n : Nat, Nat.fib (m + 3) ≤ n → exactWeightCount m n = 0) :=
  ⟨exactWeightCount_sum, fun m => by rw [exactWeightCount_zero_eq_one],
   fun m n hn => exactWeightCount_eq_zero_of_ge_fib m n hn⟩

-- Phase R607: Fiber multiplicity allFalse extended seeds
-- ══════════════════════════════════════════════════════════════

/-- fiberMultiplicity(allFalse, 4) = 3.
    thm:pom-fiberMultiplicity-allFalse -/
theorem fiberMultiplicity_allFalse_four :
    X.fiberMultiplicity (⟨fun _ => false, no11_allFalse⟩ : X 4) = 3 := by
  rw [fiberMultiplicity_allFalse_closed]

/-- fiberMultiplicity(allFalse, 5) = 3.
    thm:pom-fiberMultiplicity-allFalse -/
theorem fiberMultiplicity_allFalse_five :
    X.fiberMultiplicity (⟨fun _ => false, no11_allFalse⟩ : X 5) = 3 := by
  rw [fiberMultiplicity_allFalse_closed]

/-- fiberMultiplicity(allFalse, 6) = 4.
    thm:pom-fiberMultiplicity-allFalse -/
theorem fiberMultiplicity_allFalse_six :
    X.fiberMultiplicity (⟨fun _ => false, no11_allFalse⟩ : X 6) = 4 := by
  rw [fiberMultiplicity_allFalse_closed]

/-- Paper package: allFalse fiber multiplicity seeds.
    thm:pom-fiberMultiplicity-allFalse -/
theorem paper_fiberMultiplicity_allFalse_seeds :
    X.fiberMultiplicity (⟨fun _ => false, no11_allFalse⟩ : X 2) = 2 ∧
    X.fiberMultiplicity (⟨fun _ => false, no11_allFalse⟩ : X 3) = 2 ∧
    X.fiberMultiplicity (⟨fun _ => false, no11_allFalse⟩ : X 4) = 3 ∧
    X.fiberMultiplicity (⟨fun _ => false, no11_allFalse⟩ : X 5) = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [fiberMultiplicity_allFalse_closed]

end Omega
