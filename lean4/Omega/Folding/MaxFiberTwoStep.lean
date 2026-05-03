import Omega.Folding.MaxFiber
import Omega.Folding.Value

namespace Omega

/-- When n < fib(m+3), X.ofNat(m+2, n) has bit m+1 = false.
    infra:ofNat-last-false -/
theorem ofNat_last_false_of_lt (m n : Nat) (hn : n < Nat.fib (m + 3)) :
    (X.ofNat (m + 2) n).1 ⟨m + 1, by omega⟩ = false := by
  by_contra h
  push_neg at h
  have htrue : get (X.ofNat (m + 2) n).1 (m + 1) = true := by
    rw [get_of_lt _ (show m + 1 < m + 2 from by omega)]
    cases hb : (X.ofNat (m + 2) n).1 ⟨m + 1, by omega⟩ <;> simp_all
  have hmem : (m + 1) + 2 ∈ Nat.zeckendorf n :=
    (X.get_ofNat_eq_true_iff (show m + 1 < m + 2 from by omega)).mp htrue
  have hle := X.fib_le_of_mem_zeckendorf hmem
  simp only [show m + 1 + 2 = m + 3 from by omega] at hle
  exact absurd hn (not_lt.mpr hle)

/-- When fib(m+3) ≤ n < fib(m+4), X.ofNat(m+2, n) has bit m+1 = true.
    infra:ofNat-last-true -/
theorem ofNat_last_true_of_ge (m n : Nat)
    (hlo : Nat.fib (m + 3) ≤ n) (hhi : n < Nat.fib (m + 4)) :
    (X.ofNat (m + 2) n).1 ⟨m + 1, by omega⟩ = true := by
  have hlt : m + 1 < m + 2 := by omega
  rw [show (X.ofNat (m + 2) n).1 ⟨m + 1, by omega⟩ =
    get (X.ofNat (m + 2) n).1 (m + 1) from by rw [get_of_lt _ hlt]]
  rw [X.get_ofNat_eq_true_iff hlt]
  have hpos : 0 < n := Nat.lt_of_lt_of_le (Nat.fib_pos.mpr (by omega)) hlo
  rw [Nat.zeckendorf_of_pos hpos]
  have hGF : Nat.greatestFib n = m + 3 :=
    Nat.le_antisymm
      (Nat.lt_succ_iff.mp (Nat.greatestFib_lt.mpr hhi))
      (Nat.le_greatestFib.mpr hlo)
  rw [hGF]; simp only [show m + 1 + 2 = m + 3 from by omega]
  exact List.mem_cons_self ..

-- ══════════════════════════════════════════════════════════════
-- Hidden bit count
-- ══════════════════════════════════════════════════════════════

/-- Count of words with weight ≥ fib(m+2).
    def:pom-hidden-bit-count -/
def hiddenBitCount (m : Nat) : Nat :=
  (Finset.univ (α := Word m)).filter (fun w => Nat.fib (m + 2) ≤ weight w) |>.card

/-- thm:pom-hidden-bit-count-zero -/
theorem hiddenBitCount_zero : hiddenBitCount 0 = 0 := by decide

/-- thm:pom-hidden-bit-count-one -/
theorem hiddenBitCount_one : hiddenBitCount 1 = 0 := by decide

-- ══════════════════════════════════════════════════════════════
-- Helper: if weight w ≥ fib(m+4) for w : Word(m+2), then w[m+1]=true
-- ══════════════════════════════════════════════════════════════

private theorem last_true_of_heavy (m : Nat) (w : Word (m + 2))
    (hw : Nat.fib (m + 4) ≤ weight w) : w ⟨m + 1, by omega⟩ = true := by
  by_contra h
  have hfalse : w ⟨m + 1, by omega⟩ = false := Bool.eq_false_iff.mpr h
  have hwd : weight w = weight (truncate w) := by simp [weight, hfalse]
  -- truncate w : Word (m + 1), so weight < Nat.fib (m + 4)
  have hlt : weight (truncate w) < Nat.fib ((m + 1) + 3) := X.weight_lt_fib _
  rw [show (m + 1) + 3 = m + 4 from by omega] at hlt
  omega

-- ══════════════════════════════════════════════════════════════
-- Recurrence: hiddenBitCount (m+2) = 2^m + hiddenBitCount m
-- ══════════════════════════════════════════════════════════════

/-- thm:pom-hidden-bit-count-recurrence -/
theorem hiddenBitCount_recurrence (m : Nat) :
    hiddenBitCount (m + 2) = 2 ^ m + hiddenBitCount m := by
  unfold hiddenBitCount
  -- Abbreviations
  have hfib4 : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := by
    have := fib_succ_succ' (m + 2)
    rw [show m + 2 + 2 = m + 4 from by omega, show m + 2 + 1 = m + 3 from by omega] at this
    omega
  -- B_{m+2}: {w : Word(m+2) | fib(m+4) ≤ weight w}
  -- Split into BF = {w | ... ∧ w[m]=false} and BT = {w | ... ∧ w[m]=true}
  -- Define BF and BT as single filters on Finset.univ
  let BF := (Finset.univ (α := Word (m + 2))).filter
    (fun w => Nat.fib (m + 2 + 2) ≤ weight w ∧ w ⟨m, by omega⟩ = false)
  let BT := (Finset.univ (α := Word (m + 2))).filter
    (fun w => Nat.fib (m + 2 + 2) ≤ weight w ∧ w ⟨m, by omega⟩ = true)
  -- B = BF ∪ BT
  have hpartition : (Finset.univ (α := Word (m + 2))).filter
      (fun w => Nat.fib (m + 2 + 2) ≤ weight w) = BF ∪ BT := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, BF, BT]
    constructor
    · intro hw
      by_cases hb : w ⟨m, by omega⟩ = true
      · right; exact ⟨hw, hb⟩
      · left; exact ⟨hw, Bool.eq_false_iff.mpr hb⟩
    · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
  have hdisjoint : Disjoint BF BT := by
    simp only [BF, BT, Finset.disjoint_filter]
    intro w _ ⟨_, hF⟩ ⟨_, hT⟩; rw [hF] at hT; exact Bool.noConfusion hT
  -- |BF| = hiddenBitCount m
  have hBF_card : BF.card =
      ((Finset.univ (α := Word m)).filter (fun w => Nat.fib (m + 2) ≤ weight w)).card := by
    apply Finset.card_bij (fun w _ => truncate (truncate w))
    · -- maps into target
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, BF] at hw ⊢
      have hwt := hw.1
      have hwf := hw.2
      have hlast : w ⟨m + 1, by omega⟩ = true :=
        last_true_of_heavy m w (by rw [show m + 2 + 2 = m + 4 from by omega] at hwt; exact hwt)
      have hwd : weight w = weight (truncate (truncate w)) + Nat.fib (m + 3) := by
        conv_lhs => rw [weight_of_lastTrue hlast]
        rw [weight_of_lastFalse (show (truncate w) ⟨m, _⟩ = false by simp [truncate, hwf])]
      rw [show m + 2 + 2 = m + 4 from by omega] at hwt
      omega
    · -- injective
      intro w1 hw1 w2 hw2 heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, BF] at hw1 hw2
      have h1l : w1 ⟨m + 1, by omega⟩ = true :=
        last_true_of_heavy m w1 (by rw [show m + 2 + 2 = m + 4 from by omega] at hw1; exact hw1.1)
      have h2l : w2 ⟨m + 1, by omega⟩ = true :=
        last_true_of_heavy m w2 (by rw [show m + 2 + 2 = m + 4 from by omega] at hw2; exact hw2.1)
      funext i
      by_cases h1 : i.val < m
      · -- For i < m, use heq (truncate ∘ truncate agrees)
        have := congrFun heq ⟨i.val, h1⟩
        simp [truncate] at this
        exact this
      · by_cases h2 : i.val = m
        · -- At position m, both are false
          have hi : i = ⟨m, by omega⟩ := Fin.ext h2
          rw [hi, hw1.2, hw2.2]
        · -- At position m+1, both are true
          have h3 : i.val = m + 1 := by omega
          have hi : i = ⟨m + 1, by omega⟩ := Fin.ext h3
          rw [hi, h1l, h2l]
    · -- surjective
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      refine ⟨snoc (snoc u false) true, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, BF]
      refine ⟨?_, ?_⟩
      · show Nat.fib (m + 2 + 2) ≤ weight (snoc (snoc u false) true)
        rw [weight_snoc, weight_snoc]
        simp only [Bool.false_eq_true, ite_false, Nat.add_zero, ite_true]
        rw [show m + 2 + 2 = m + 4 from by omega, show m + 1 + 2 = m + 3 from by omega]; omega
      · show snoc (snoc u false) true ⟨m, by omega⟩ = false
        simp [snoc, show m < m + 1 from by omega]
  -- |BT| = 2^m
  have hBT_card : BT.card = 2 ^ m := by
    have hcard_word : (Finset.univ (α := Word m)).card = 2 ^ m := by
      simp [Fintype.card_fin, Fintype.card_bool]
    rw [← hcard_word]; symm
    apply Finset.card_bij (fun w _ => snoc (snoc w true) true)
    · -- maps into target
      intro w _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, BT]
      refine ⟨?_, ?_⟩
      · show Nat.fib (m + 2 + 2) ≤ weight (snoc (snoc w true) true)
        rw [weight_snoc, weight_snoc]; simp only [ite_true]
        rw [show m + 2 + 2 = m + 4 from by omega, show m + 1 + 2 = m + 3 from by omega]; omega
      · show snoc (snoc w true) true ⟨m, by omega⟩ = true
        simp [snoc, show m < m + 1 from by omega]
    · -- injective
      intro w1 _ w2 _ h
      have : ∀ i : Fin m, w1 i = w2 i := by
        intro i
        have := congr_fun h (⟨i.val, by omega⟩ : Fin (m + 2))
        simp [snoc, show i.val < m from i.isLt, show i.val < m + 1 from by omega] at this
        exact this
      exact funext this
    · -- surjective
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, BT] at hw
      have hwt := hw.1
      have hwb := hw.2
      have hlast : w ⟨m + 1, by omega⟩ = true := by
        apply last_true_of_heavy m w
        rw [show m + 2 + 2 = m + 4 from by omega] at hwt; exact hwt
      refine ⟨truncate (truncate w), Finset.mem_univ _, ?_⟩
      funext i
      by_cases h1 : i.val < m
      · simp [snoc, truncate, h1, show i.val < m + 1 from by omega]
      · by_cases h2 : i.val = m
        · have hi : (⟨m, by omega⟩ : Fin (m + 2)) = i := Fin.ext h2.symm
          rw [← hi]; simp [snoc, show m < m + 1 from by omega, hwb]
        · have h3 : i.val = m + 1 := by omega
          have hi : (⟨m + 1, by omega⟩ : Fin (m + 2)) = i := Fin.ext h3.symm
          rw [← hi]; simp [snoc, hlast]
  -- Combine
  rw [hpartition, Finset.card_union_of_disjoint hdisjoint, hBF_card, hBT_card]
  omega

-- ══════════════════════════════════════════════════════════════
-- Closed form: hiddenBitCount m * 3 + δ = 2^m
-- ══════════════════════════════════════════════════════════════

/-- thm:pom-hidden-bit-count-closed -/
theorem hiddenBitCount_closed (m : Nat) :
    hiddenBitCount m * 3 + (if m % 2 = 0 then 1 else 2) = 2 ^ m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => simp [hiddenBitCount_zero]
    | 1 => simp [hiddenBitCount_one]
    | m + 2 =>
      rw [hiddenBitCount_recurrence]
      have ihm := ih m (by omega)
      have hmod : (m + 2) % 2 = m % 2 := by omega
      rw [hmod]
      have h2 : 2 ^ (m + 2) = 4 * 2 ^ m := by ring
      omega

-- ══════════════════════════════════════════════════════════════
-- Phase R320: hiddenBitCount mod 3 periodicity
-- ══════════════════════════════════════════════════════════════

/-- Hidden bit count mod 3 has period 6: B(m+6) % 3 = B(m) % 3.
    thm:pom-hidden-bit-count -/
theorem hiddenBitCount_period6_mod3 (m : Nat) :
    hiddenBitCount (m + 6) % 3 = hiddenBitCount m % 3 := by
  -- B(m+6) = 2^(m+4) + B(m+4) = 2^(m+4) + 2^(m+2) + B(m+2)
  --        = 2^(m+4) + 2^(m+2) + 2^m + B(m)
  rw [hiddenBitCount_recurrence (m + 4), hiddenBitCount_recurrence (m + 2),
      hiddenBitCount_recurrence m]
  -- Goal: (2^(m+4) + (2^(m+2) + (2^m + B(m)))) % 3 = B(m) % 3
  -- 2^(m+4) + 2^(m+2) + 2^m = 2^m * (16 + 4 + 1) = 21 * 2^m
  have : 2 ^ (m + 4) + 2 ^ (m + 2) + 2 ^ m = 21 * 2 ^ m := by ring
  omega

-- ══════════════════════════════════════════════════════════════
-- lem:pom-one-bit: single hidden bit decomposition
-- ══════════════════════════════════════════════════════════════

/-- The hidden bit: 1 if weight w ≥ fib(m+2), else 0.
    def:pom-hidden-bit -/
def hiddenBit (w : Word m) : Nat :=
  if Nat.fib (m + 2) ≤ weight w then 1 else 0

/-- lem:pom-hidden-bit-le-one -/
theorem hiddenBit_le_one (w : Word m) : hiddenBit w ≤ 1 := by
  unfold hiddenBit; split <;> omega

/-- When fib(m+2) ≤ n < fib(m+3), X.ofNat m n = X.ofNat m (n - fib(m+2)).
    The Zeckendorf head index m+2 is invisible at level m.
    lem:pom-ofNat-sub-fib -/
theorem ofNat_sub_fib_of_ge (m n : Nat)
    (hlo : Nat.fib (m + 2) ≤ n) (hhi : n < Nat.fib (m + 3)) :
    X.ofNat m n = X.ofNat m (n - Nat.fib (m + 2)) := by
  apply Subtype.ext; funext j
  simp only [X.ofNat, X.ofIndices, X.wordOfIndices]; congr 1; apply propext
  -- Goal: j.1 + 2 ∈ Nat.zeckendorf n ↔ j.1 + 2 ∈ Nat.zeckendorf (n - fib(m+2))
  change j.1 + 2 ∈ Nat.zeckendorf n ↔ j.1 + 2 ∈ Nat.zeckendorf (n - Nat.fib (m + 2))
  have hpos : 0 < n := Nat.lt_of_lt_of_le (Nat.fib_pos.mpr (by omega)) hlo
  -- greatestFib n = m + 2
  have hGF : Nat.greatestFib n = m + 2 :=
    Nat.le_antisymm
      (Nat.lt_succ_iff.mp (Nat.greatestFib_lt.mpr hhi))
      (Nat.le_greatestFib.mpr hlo)
  -- zeckendorf n = (m+2) :: zeckendorf (n - fib(m+2))
  rw [Nat.zeckendorf_of_pos hpos, hGF]
  -- Goal: j.1 + 2 ∈ (m + 2) :: Nat.zeckendorf (n - fib(m+2)) ↔
  --       j.1 + 2 ∈ Nat.zeckendorf (n - fib(m+2))
  simp only [List.mem_cons]
  -- j.1 + 2 = m + 2 ∨ j.1 + 2 ∈ tail ↔ j.1 + 2 ∈ tail
  -- Since j : Fin m, j.1 < m, so j.1 + 2 < m + 2, hence j.1 + 2 ≠ m + 2
  constructor
  · intro h; rcases h with heq | htail
    · exfalso; omega
    · exact htail
  · exact Or.inr

/-- lem:pom-one-bit: weight(w) = stableValue(Fold(w)) + hiddenBit(w) · fib(m+2). -/
theorem weight_eq_stableValue_add_hiddenBit (w : Word m) :
    weight w = stableValue (Fold w) + hiddenBit w * Nat.fib (m + 2) := by
  unfold hiddenBit Fold
  have hwlt : weight w < Nat.fib (m + 3) := X.weight_lt_fib w
  by_cases hge : Nat.fib (m + 2) ≤ weight w
  · -- Case b=1: weight w ≥ fib(m+2)
    simp only [hge, ite_true, one_mul]
    -- Fold w = X.ofNat m (weight w)
    -- By ofNat_sub_fib_of_ge: X.ofNat m (weight w) = X.ofNat m (weight w - fib(m+2))
    have hsub : X.ofNat m (weight w) = X.ofNat m (weight w - Nat.fib (m + 2)) :=
      ofNat_sub_fib_of_ge m (weight w) hge hwlt
    rw [hsub]
    -- weight w - fib(m+2) < fib(m+1) < fib(m+2)
    have hrem_lt : weight w - Nat.fib (m + 2) < Nat.fib (m + 2) := by
      have hfib3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
      have : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
      omega
    rw [X.stableValue_ofNat_lt _ hrem_lt]
    omega
  · -- Case b=0: weight w < fib(m+2)
    push_neg at hge
    simp only [show ¬ (Nat.fib (m + 2) ≤ weight w) from by omega, ite_false, zero_mul,
      Nat.add_zero]
    rw [X.stableValue_ofNat_lt _ hge]

-- ══════════════════════════════════════════════════════════════
-- stableValue of Fold as modular reduction
-- ══════════════════════════════════════════════════════════════

/-- stableValue of Fold w equals weight w mod F_{m+2}.
    lem:pom-stableValue-Fold-mod -/
theorem stableValue_Fold_mod (w : Word m) :
    stableValue (Fold w) = weight w % Nat.fib (m + 2) := by
  have h := weight_eq_stableValue_add_hiddenBit w
  have hlt := stableValue_lt_fib (Fold w)
  have hfib_pos : 0 < Nat.fib (m + 2) := fib_succ_pos (m + 1)
  -- weight w = sv + b * F, sv < F  ⟹  sv = weight w % F
  rw [h, Nat.add_mul_mod_self_right]
  exact (Nat.mod_eq_of_lt hlt).symm

-- ══════════════════════════════════════════════════════════════
-- lem:pom-fold-congruence: Fold(w) = Fold(w') iff weight congruent mod F_{m+2}
-- ══════════════════════════════════════════════════════════════

/-- lem:pom-fold-congruence: Fold(w) = Fold(w') iff weight(w) ≡ weight(w') (mod F_{m+2}). -/
theorem Fold_eq_iff_weight_mod {m : Nat} (w w' : Word m) :
    Fold w = Fold w' ↔ weight w % Nat.fib (m + 2) = weight w' % Nat.fib (m + 2) := by
  constructor
  · intro h
    rw [← stableValue_Fold_mod w, ← stableValue_Fold_mod w', h]
  · intro h
    have hsv : stableValue (Fold w) = stableValue (Fold w') := by
      rw [stableValue_Fold_mod w, stableValue_Fold_mod w', h]
    exact X.stableValueFin_injective m (by simp [X.stableValueFin, hsv])
-- ══════════════════════════════════════════════════════════════
-- Fiber membership via weight congruence
-- ══════════════════════════════════════════════════════════════

/-- The fiber of x is exactly {w : weight w % F_{m+2} = stableValue x}.
    cor:pom-mem-fiber-weight-mod -/
theorem mem_fiber_iff_weight_mod (x : X m) (w : Word m) :
    w ∈ X.fiber x ↔ weight w % Nat.fib (m + 2) = stableValue x := by
  rw [X.mem_fiber]
  constructor
  · -- (→) Fold w = x → weight w % F = stableValue x
    intro h
    rw [← h, stableValue_Fold_mod]
  · -- (←) weight w % F = stableValue x → Fold w = x
    intro h
    -- stableValue x = weight x.1, and weight x.1 < fib(m+2), so stableValue x % F = stableValue x
    have hlt : stableValue x < Nat.fib (m + 2) := stableValue_lt_fib x
    have hmod_x : weight x.1 % Nat.fib (m + 2) = stableValue x :=
      Nat.mod_eq_of_lt hlt
    -- So weight w % F = weight x.1 % F
    rw [← hmod_x] at h
    -- By Fold_eq_iff_weight_mod: Fold w = Fold x.1
    rw [← Fold_stable x]
    exact (Fold_eq_iff_weight_mod w x.1).mpr h

-- ══════════════════════════════════════════════════════════════
-- fiberMultiplicity as weight congruence count
-- ══════════════════════════════════════════════════════════════

/-- fiberMultiplicity x = #{w : weight w % F_{m+2} = stableValue x}.
    cor:pom-fiberMultiplicity-weight-congr -/
theorem fiberMultiplicity_eq_weight_congr_count (x : X m) :
    X.fiberMultiplicity x =
    (Finset.univ.filter (fun w : Word m =>
      weight w % Nat.fib (m + 2) = stableValue x)).card := by
  unfold X.fiberMultiplicity
  congr 1; ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_fiber_iff_weight_mod x w

-- ══════════════════════════════════════════════════════════════
-- Pointwise fiber recurrence: d_{m+2}(x) ≤ d_{m+1}(restrict x) + d_m(restrict² x)
-- ══════════════════════════════════════════════════════════════

/-- Weight of a word with last bit true decomposes into double-truncate + mid-bit + last-fib. -/
private theorem weight_expand' {m : Nat} (w : Word (m + 2)) (hLast : w ⟨m + 1, by omega⟩ = true) :
    weight w = weight (truncate (truncate w)) +
    (if w ⟨m, by omega⟩ = true then Nat.fib (m + 2) else 0) + Nat.fib (m + 3) := by
  have h1 : weight w = weight (truncate w) + Nat.fib (m + 3) := by
    rw [weight]; simp only [hLast, ↓reduceIte]
  have h2 : weight (truncate w) = weight (truncate (truncate w)) +
      (if (truncate w) ⟨m, Nat.lt_succ_self m⟩ = true then Nat.fib (m + 2) else 0) := by
    rw [weight]
  have h3 : (truncate w) ⟨m, Nat.lt_succ_self m⟩ = w ⟨m, by omega⟩ := by
    simp [truncate]
  rw [h1, h2, h3]

/-- Pointwise: d_{m+2}(x) ≤ d_{m+1}(restrict x) + d_m(restrict² x).
    thm:pom-fiberMultiplicity-le-restrict-add -/
theorem fiberMultiplicity_le_restrict_add (x : X (m + 2)) :
    X.fiberMultiplicity x ≤
    X.fiberMultiplicity (X.restrict x) + X.fiberMultiplicity (X.restrict (X.restrict x)) := by
  classical
  -- False-ending bound: #{w ∈ fiber(x) | w[m+1]=false} ≤ |fiber(restrict x)|
  have hFalse : ((X.fiber x).filter (fun w => w ⟨m+1, by omega⟩ = false)).card ≤
      (X.fiber (X.restrict x)).card :=
    Finset.card_le_card_of_injOn truncate
      (fun w hw => by
        rw [Finset.mem_coe, Finset.mem_filter] at hw; rw [Finset.mem_coe, X.mem_fiber]
        have hFold := X.mem_fiber.mp hw.1; have hLast := hw.2
        rw [← X.snoc_truncate_last w] at hFold; rw [hLast] at hFold
        rw [← restrict_Fold_snoc_false (truncate w)]; exact congrArg X.restrict hFold)
      (fun w₁ hw₁ w₂ hw₂ hEq => by
        rw [Finset.mem_coe, Finset.mem_filter] at hw₁ hw₂
        rw [← X.snoc_truncate_last w₁, ← X.snoc_truncate_last w₂, hEq, hw₁.2, hw₂.2])
  -- True-ending bound: #{w ∈ fiber(x) | w[m+1]=true} ≤ |fiber(restrict(restrict x))|
  have hTrue : ((X.fiber x).filter (fun w => w ⟨m+1, by omega⟩ = true)).card ≤
      (X.fiber (X.restrict (X.restrict x))).card :=
    Finset.card_le_card_of_injOn (fun w => truncate (truncate w))
      (fun w hw => by
        rw [Finset.mem_coe, Finset.mem_filter] at hw; rw [Finset.mem_coe, X.mem_fiber]
        have hFold := X.mem_fiber.mp hw.1; have hLast := hw.2
        have hWT := X.weight_lt_fib (truncate (truncate w))
        show Fold (truncate (truncate w)) = X.restrict (X.restrict x)
        rw [← hFold]; simp only [Fold, restrict_ofNat]
        rw [weight_expand' w hLast]
        cases hMid : w ⟨m, by omega⟩
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          exact (X.ofNat_add_fib (m + 2) (le_refl _) _ hWT).symm
        · simp only [↓reduceIte]
          rw [show weight (truncate (truncate w)) + Nat.fib (m + 2) + Nat.fib (m + 3) =
              weight (truncate (truncate w)) + (Nat.fib (m + 3) + Nat.fib (m + 2)) from by ring,
              fib_add_succ (m + 1)]
          exact (X.ofNat_add_fib (m + 3) (by omega) _
            (Nat.lt_of_lt_of_le hWT (Nat.fib_mono (by omega)))).symm)
      (fun w₁ hw₁ w₂ hw₂ hEq => by
        rw [Finset.mem_coe, Finset.mem_filter] at hw₁ hw₂
        have hL1 := hw₁.2; have hL2 := hw₂.2
        have hWT := X.weight_lt_fib (truncate (truncate w₁))
        have hMidEq : w₁ ⟨m, by omega⟩ = w₂ ⟨m, by omega⟩ := by
          by_contra hne
          have hFE : X.ofNat (m + 2) (weight w₁) = X.ofNat (m + 2) (weight w₂) := by
            change Fold w₁ = Fold w₂
            exact (X.mem_fiber.mp hw₁.1).trans (X.mem_fiber.mp hw₂.1).symm
          have hWEq : weight (truncate (truncate w₁)) = weight (truncate (truncate w₂)) :=
            congr_arg weight hEq
          rw [weight_expand' w₁ hL1, weight_expand' w₂ hL2, hWEq] at hFE
          cases h₁ : w₁ ⟨m, by omega⟩ <;> cases h₂ : w₂ ⟨m, by omega⟩
          <;> simp only [h₁, h₂, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hFE
          · exact absurd (by rw [h₁, h₂]) hne
          · exfalso
            apply X.ofNat_ne_of_shift (weight (truncate (truncate w₂))) (hWEq ▸ hWT)
            have hRec : Nat.fib (m + 3) + Nat.fib (m + 2) = Nat.fib (m + 4) :=
              fib_add_succ (m + 1)
            exact hFE.trans (congr_arg (X.ofNat (m + 2)) (by omega))
          · exfalso
            apply X.ofNat_ne_of_shift (weight (truncate (truncate w₂))) (hWEq ▸ hWT)
            have hRec : Nat.fib (m + 3) + Nat.fib (m + 2) = Nat.fib (m + 4) :=
              fib_add_succ (m + 1)
            exact hFE.symm.trans (congr_arg (X.ofNat (m + 2)) (by omega))
          · exact absurd (by rw [h₁, h₂]) hne
        have hTrEq : truncate w₁ = truncate w₂ := by
          rw [← X.snoc_truncate_last (truncate w₁), ← X.snoc_truncate_last (truncate w₂)]
          exact congr_arg₂ snoc hEq hMidEq
        rw [← X.snoc_truncate_last w₁, ← X.snoc_truncate_last w₂, hL1, hL2, hTrEq])
  -- Combine
  calc X.fiberMultiplicity x = (X.fiber x).card := rfl
    _ = ((X.fiber x).filter (fun w => w ⟨m+1, by omega⟩ = false)).card +
        ((X.fiber x).filter (fun w => w ⟨m+1, by omega⟩ = true)).card := by
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun w _ h1 h2 => by
        rw [h1] at h2; exact Bool.false_ne_true h2)]
      congr 1; ext w; simp only [Finset.mem_union, Finset.mem_filter]
      exact ⟨fun h => by cases w ⟨m+1, by omega⟩ <;> simp_all, fun h => h.elim And.left And.left⟩
    _ ≤ _ := Nat.add_le_add hFalse hTrue

-- ══════════════════════════════════════════════════════════════
-- Fold uniqueness
-- ══════════════════════════════════════════════════════════════

/-- Any retraction preserving weight congruence must equal Fold.
    thm:fold-congruence-universal-property -/
theorem Fold_unique_of_weight_congr {m : Nat} (Φ : Word m → X m)
    (hΦ : ∀ w, stableValue (Φ w) % Nat.fib (m + 2) = weight w % Nat.fib (m + 2)) :
    ∀ w, Φ w = Fold w := by
  intro w
  have hlt := stableValue_lt_fib (Φ w)
  have hΦw := hΦ w
  rw [Nat.mod_eq_of_lt hlt] at hΦw
  have heq : stableValue (Φ w) = stableValue (Fold w) := by
    rw [hΦw, stableValue_Fold_mod]
  exact X.stableValueFin_injective m (by simp [X.stableValueFin, heq])

/-- Fold uniqueness with explicit retraction hypothesis (corollary).
    thm:fold-unique-of-retraction -/
theorem Fold_unique_of_retraction {m : Nat} (Φ : Word m → X m)
    (_hRetract : ∀ x : X m, Φ x.1 = x)
    (hCongr : ∀ w, stableValue (Φ w) % Nat.fib (m + 2) = weight w % Nat.fib (m + 2)) :
    ∀ w, Φ w = Fold w :=
  Fold_unique_of_weight_congr Φ hCongr

/-- Two stable words with equal stableValue are equal.
    thm:pom-eq-of-stableValue-eq -/
theorem X.eq_of_stableValue_eq' {x y : X m} (h : stableValue x = stableValue y) : x = y :=
  X.stableValueFin_injective m (by simp [X.stableValueFin, h])

/-- Any weight-congruence-preserving map is constant on fibers.
    thm:pom-congr-map-fiber-const -/
theorem congr_map_fiber_const {m : Nat} (Φ : Word m → X m)
    (hΦ : ∀ w, stableValue (Φ w) % Nat.fib (m + 2) = weight w % Nat.fib (m + 2))
    (w₁ w₂ : Word m) (h : Fold w₁ = Fold w₂) : Φ w₁ = Φ w₂ := by
  rw [Fold_unique_of_weight_congr Φ hΦ w₁, Fold_unique_of_weight_congr Φ hΦ w₂, h]

/-- The preimage of any weight-congruence map equals the Fold fiber.
    thm:pom-fiber-independent-of-retraction -/
theorem fiber_independent_of_retraction {m : Nat} (Φ : Word m → X m)
    (hΦ : ∀ w, stableValue (Φ w) % Nat.fib (m + 2) = weight w % Nat.fib (m + 2))
    (x : X m) : {w : Word m | Φ w = x} = {w : Word m | Fold w = x} := by
  ext w; have huniq := Fold_unique_of_weight_congr Φ hΦ w
  simp only [Set.mem_setOf_eq]; constructor
  · intro h; rw [← huniq]; exact h
  · intro h; rw [huniq]; exact h

-- ══════════════════════════════════════════════════════════════
-- Fold-snoc decomposition
-- ══════════════════════════════════════════════════════════════

/-- thm:pom-restrict-Fold-eq -/
theorem restrict_Fold_eq (w : Word (m + 1)) :
    X.restrict (Fold w) = X.ofNat m (weight w) := by
  unfold Fold; exact restrict_ofNat m (weight w)

/-- thm:pom-Fold-snoc-false-eq -/
theorem Fold_snoc_false_eq (w : Word m) :
    Fold (snoc w false) = X.ofNat (m + 1) (weight w) := by
  unfold Fold; congr 1; rw [weight_snoc]; simp

/-- thm:pom-Fold-snoc-true-eq -/
theorem Fold_snoc_true_eq (w : Word m) :
    Fold (snoc w true) = X.ofNat (m + 1) (weight w + Nat.fib (m + 2)) := by
  unfold Fold; congr 1; rw [weight_snoc]; simp

/-- thm:pom-stableValue-Fold-snoc-false -/
theorem stableValue_Fold_snoc_false (w : Word m) :
    stableValue (Fold (snoc w false)) = weight w % Nat.fib (m + 3) := by
  rw [stableValue_Fold_mod, weight_snoc]; simp

/-- thm:pom-stableValue-Fold-snoc-true -/
theorem stableValue_Fold_snoc_true (w : Word m) :
    stableValue (Fold (snoc w true)) =
    (weight w + Nat.fib (m + 2)) % Nat.fib (m + 3) := by
  rw [stableValue_Fold_mod, weight_snoc]; simp

/-- Paper theorem: hidden bit count recurrence bundle.
    thm:pom-hidden-bit-count -/
theorem paper_hiddenBitCount_recurrence :
    hiddenBitCount 0 = 0 ∧ hiddenBitCount 1 = 0 ∧
    (∀ m, hiddenBitCount (m + 2) = 2 ^ m + hiddenBitCount m) :=
  ⟨hiddenBitCount_zero, hiddenBitCount_one, hiddenBitCount_recurrence⟩

/-- Paper label: hidden bit count closed form.
    thm:pom-hidden-bit-count -/
theorem paper_hiddenBitCount_closed (m : Nat) :
    3 * hiddenBitCount m + (if m % 2 = 0 then 1 else 2) = 2 ^ m := by
  have := hiddenBitCount_closed m; omega

-- ══════════════════════════════════════════════════════════════
-- Phase R13: hiddenBitCount even/odd closed forms
-- ══════════════════════════════════════════════════════════════

/-- 2^(2k) = 4^k. -/
private theorem two_pow_two_mul (k : Nat) : 2 ^ (2 * k) = 4 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [show 2 * (k + 1) = 2 * k + 2 from by omega, pow_add]; simp [ih]; ring

/-- 3·A(2k) = 4^k - 1 for k ≥ 1.
    thm:fold-top-two-zeckendorf-trisect -/
theorem hiddenBitCount_even_closed (k : Nat) (_hk : 1 ≤ k) :
    3 * hiddenBitCount (2 * k) = 4 ^ k - 1 := by
  have h := hiddenBitCount_closed (2 * k)
  have hmod : (2 * k) % 2 = 0 := by omega
  simp only [hmod, ite_true] at h
  rw [two_pow_two_mul] at h
  omega

/-- 3·A(2k+1) = 2·4^k - 2 for all k.
    thm:fold-top-two-zeckendorf-trisect -/
theorem hiddenBitCount_odd_closed (k : Nat) :
    3 * hiddenBitCount (2 * k + 1) = 2 * 4 ^ k - 2 := by
  have h := paper_hiddenBitCount_closed (2 * k + 1)
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  rw [hmod] at h; simp at h
  -- h : 3 * hiddenBitCount (2 * k + 1) + 2 = 2 ^ (2 * k + 1)
  have h4 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    have : 2 ^ (2 * k + 1) = 2 ^ (2 * k) * 2 := pow_succ 2 (2 * k)
    rw [two_pow_two_mul] at this; linarith
  have hge : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by omega)
  omega

/-- Fold + hiddenBit jointly determine weight.
    prop:pom-fold-prime-lift-injective -/
theorem fold_hiddenBit_determines_weight (w1 w2 : Word m)
    (hFold : Fold w1 = Fold w2) (hBit : hiddenBit w1 = hiddenBit w2) :
    weight w1 = weight w2 := by
  have h1 := weight_eq_stableValue_add_hiddenBit w1
  have h2 := weight_eq_stableValue_add_hiddenBit w2
  rw [h1, h2]; congr 1
  · exact congrArg stableValue hFold
  · rw [hBit]

/-- Paper-facing wrapper for the fold + hiddenBit injective seed.
    prop:pom-fold-prime-lift-injective -/
theorem paper_pom_fold_prime_lift_injective_seeds_wrap (w1 w2 : Word m)
    (hFold : Fold w1 = Fold w2) (hBit : hiddenBit w1 = hiddenBit w2) :
    weight w1 = weight w2 :=
  fold_hiddenBit_determines_weight w1 w2 hFold hBit

theorem paper_pom_fold_prime_lift_injective_package (w1 w2 : Word m)
    (hFold : Fold w1 = Fold w2) (hBit : hiddenBit w1 = hiddenBit w2) :
    weight w1 = weight w2 :=
  paper_pom_fold_prime_lift_injective_seeds_wrap w1 w2 hFold hBit

-- ══════════════════════════════════════════════════════════════
-- Phase 146: weight truncation mod + curvature = hiddenBit
-- ══════════════════════════════════════════════════════════════

/-- weight(truncate w) ≡ weight(w) mod F_{m+2}: the last bit contributes a full F_{m+2}.
    bridge:weight-truncate-mod -/
theorem weight_truncate_mod (w : Word (m + 1)) :
    weight (truncate w) % Nat.fib (m + 2) = weight w % Nat.fib (m + 2) := by
  have : weight w % Nat.fib (m + 2) = weight (truncate w) % Nat.fib (m + 2) := by
    conv_lhs => rw [show weight w = weight (truncate w) +
      if w ⟨m, Nat.lt_succ_self m⟩ = true then Nat.fib (m + 2) else 0 from rfl]
    split_ifs
    · rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
    · rfl
  exact this.symm

set_option maxHeartbeats 400000 in
/-- thm:pom-truncation-curvature-equals-hidden-bit:
    The curvature indicator (Fold ∘ truncate ≠ restrict ∘ Fold) equals the hidden bit. -/
theorem truncation_curvature_eq_hiddenBit (w : Word (m + 1)) :
    (if Fold (truncate w) = X.restrict (Fold w) then 0 else 1) = hiddenBit w := by
  -- Key: Fold(truncate w) and X.restrict(Fold w) in X m agree iff stableValues match
  -- stableValue(Fold(truncate w)) = weight(truncate w) % F_{m+2}
  -- stableValue(restrict(Fold w)) = (weight w % F_{m+3}) % F_{m+2}
  -- hiddenBit w = if F_{(m+1)+2} ≤ weight w then 1 else 0
  have hlt_tr : weight (truncate w) < Nat.fib (m + 3) := X.weight_lt_fib (truncate w)
  have hlt_w : weight w < Nat.fib (m + 4) := X.weight_lt_fib w
  have hfib3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  have hwt_def : weight w = weight (truncate w) +
      if w ⟨m, Nat.lt_succ_self m⟩ = true then Nat.fib (m + 2) else 0 := rfl
  -- Fold equality ↔ stableValue equality at level m
  have fold_eq_iff_sv : Fold (truncate w) = X.restrict (Fold w) ↔
      weight (truncate w) % Nat.fib (m + 2) =
      (weight w % Nat.fib (m + 3)) % Nat.fib (m + 2) := by
    constructor
    · intro h
      have := congr_arg stableValue h
      rw [stableValue_Fold_mod] at this
      have hrestr : stableValue (X.restrict (Fold w)) =
          (weight w % Nat.fib (m + 3)) % Nat.fib (m + 2) := by
        have h2 := stableValue_restrict_mod (Fold w)
        rw [Nat.mod_eq_of_lt (stableValue_lt_fib (X.restrict (Fold w)))] at h2
        rw [← h2, stableValue_Fold_mod]
      rwa [hrestr] at this
    · intro h
      apply X.stableValueFin_injective m
      simp only [X.stableValueFin, Fin.mk.injEq]
      rw [stableValue_Fold_mod]
      have hrestr : stableValue (X.restrict (Fold w)) =
          (weight w % Nat.fib (m + 3)) % Nat.fib (m + 2) := by
        have h2 := stableValue_restrict_mod (Fold w)
        rw [Nat.mod_eq_of_lt (stableValue_lt_fib (X.restrict (Fold w)))] at h2
        rw [← h2, stableValue_Fold_mod]
      rwa [hrestr]
  -- Case split on hiddenBit (= whether weight w ≥ F_{m+3})
  -- Note: hiddenBit w uses F_{(m+1)+2} = F_{m+3}
  show (if Fold (truncate w) = X.restrict (Fold w) then 0 else 1) =
    if Nat.fib (m + 1 + 2) ≤ weight w then 1 else 0
  by_cases hge : Nat.fib (m + 3) ≤ weight w
  · -- hiddenBit = 1
    have hge' : Nat.fib (m + 1 + 2) ≤ weight w := by omega
    simp only [hge', ite_true]
    -- Fold(truncate w) ≠ restrict(Fold w)
    have hneq : ¬ (Fold (truncate w) = X.restrict (Fold w)) := by
      rw [fold_eq_iff_sv]; intro hmod
      -- weight w % F_{m+3} = weight w - F_{m+3} (since weight w < 2·F_{m+3})
      have hfib4 : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := Nat.fib_add_two
      have hrem : weight w - Nat.fib (m + 3) < Nat.fib (m + 2) := by omega
      have hrem2 : weight w - Nat.fib (m + 3) < Nat.fib (m + 3) := by omega
      have : weight w % Nat.fib (m + 3) = weight w - Nat.fib (m + 3) := by
        rw [Nat.mod_eq_sub_mod hge]; exact Nat.mod_eq_of_lt hrem2
      rw [this, Nat.mod_eq_of_lt hrem] at hmod
      -- hmod: wt_tr % F_{m+2} = weight w - F_{m+3}
      -- Express weight w - F_{m+3} in terms of weight(truncate w)
      -- weight w = weight(truncate w) + (last ? F_{m+2} : 0)
      -- If last=false: weight w = weight(truncate w) < F_{m+3}, contradicts hge
      -- If last=true: weight w - F_{m+3} = weight(truncate w) + F_{m+2} - (F_{m+1}+F_{m+2}) = wt_tr - F_{m+1}
      by_cases hlast : w ⟨m, Nat.lt_succ_self m⟩ = true
      · simp only [hlast, ite_true] at hwt_def
        -- weight w - F_{m+3} = weight(truncate w) - F_{m+1}
        have hge_m1 : Nat.fib (m + 1) ≤ weight (truncate w) := by omega
        have : weight w - Nat.fib (m + 3) = weight (truncate w) - Nat.fib (m + 1) := by omega
        rw [this] at hmod
        -- wt_tr % F_{m+2} = wt_tr - F_{m+1} with F_{m+1} > 0
        have hfib1_pos : 0 < Nat.fib (m + 1) := Nat.fib_pos.mpr (by omega)
        have hfib_mono : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
        by_cases hlt2 : weight (truncate w) < Nat.fib (m + 2)
        · rw [Nat.mod_eq_of_lt hlt2] at hmod; omega
        · push_neg at hlt2
          have hsub_lt : weight (truncate w) - Nat.fib (m + 2) < Nat.fib (m + 2) := by omega
          rw [Nat.mod_eq_sub_mod hlt2, Nat.mod_eq_of_lt hsub_lt] at hmod
          -- hmod: wt - F_{m+2} = wt - F_{m+1}, so F_{m+2} = F_{m+1}
          -- But F_{m+2} = F_{m+1} + F_m with F_m ≥ 0, and hfib_mono shows F_{m+1} ≤ F_{m+2}
          -- Need: F_{m+2} > F_{m+1} (which requires F_m > 0, i.e., m > 0)
          -- For m=0: weight(truncate w) = weight(Word 0) = 0, but hge_m1: F_1=1 ≤ 0, contradiction
          -- F_{m+2} = F_m + F_{m+1}, so F_{m+2} ≠ F_{m+1} unless F_m = 0
          have hfib2 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
          have hfib_m_pos : 0 < Nat.fib m := by
            rcases m with _ | m
            · -- m = 0: weight(truncate w : Word 0) = 0, hge_m1: F_1 ≤ 0, contradiction
              simp [weight] at hge_m1
            · exact Nat.fib_pos.mpr (by omega)
          omega
      · -- last = false: weight w = weight(truncate w), contradicts hge
        exfalso
        have hf : w ⟨m, Nat.lt_succ_self m⟩ = false := Bool.eq_false_iff.mpr hlast
        have hwt_false : weight w = weight (truncate w) := by
          show weight (truncate w) + (if w ⟨m, Nat.lt_succ_self m⟩ = true then _ else 0) =
            weight (truncate w)
          simp [hf]
        omega
    simp only [hneq, ite_false]
  · -- hiddenBit = 0
    push_neg at hge
    have hge' : ¬ (Nat.fib (m + 1 + 2) ≤ weight w) := by
      show ¬ (Nat.fib (m + 3) ≤ weight w); omega
    simp only [hge', ite_false]
    -- Fold(truncate w) = restrict(Fold w)
    have heq : Fold (truncate w) = X.restrict (Fold w) := by
      rw [fold_eq_iff_sv, Nat.mod_eq_of_lt (by omega : weight w < Nat.fib (m + 3))]
      exact weight_truncate_mod w
    simp only [heq, ite_true]

/-- Paper-facing wrapper for the truncation-curvature/hiddenBit identity.
    thm:pom-truncation-curvature-equals-hidden-bit -/
theorem paper_pom_truncation_curvature_equals_hidden_bit (w : Word (m + 1)) :
    (if Fold (truncate w) = X.restrict (Fold w) then 0 else 1) = hiddenBit w :=
  truncation_curvature_eq_hiddenBit w

-- ══════════════════════════════════════════════════════════════
-- Phase R14: hiddenBitCount bounds
-- ══════════════════════════════════════════════════════════════

/-- #{weight < F} = 2^m - hiddenBitCount.
    thm:fold-top-two-zeckendorf-trisect -/
theorem complement_hiddenBitCount (m : Nat) :
    (Finset.univ.filter (fun w : Word m => weight w < Nat.fib (m + 2))).card =
    2 ^ m - hiddenBitCount m := by
  have hle : hiddenBitCount m ≤ 2 ^ m := by
    unfold hiddenBitCount
    calc (Finset.univ.filter (fun w : Word m => Nat.fib (m + 2) ≤ weight w)).card
        ≤ (Finset.univ : Finset (Word m)).card := Finset.card_filter_le _ _
      _ = 2 ^ m := by simp [ Fintype.card_bool]
  have htotal : (Finset.univ : Finset (Word m)).card = 2 ^ m := by
    simp [ Fintype.card_bool]
  have hcompl : (Finset.univ.filter (fun w : Word m => weight w < Nat.fib (m + 2))).card +
      (Finset.univ.filter (fun w : Word m => Nat.fib (m + 2) ≤ weight w)).card =
      (Finset.univ : Finset (Word m)).card := by
    rw [← Finset.card_union_of_disjoint (by
      apply Finset.disjoint_filter.mpr; intro w _ h1 h2; omega)]
    congr 1; ext w; simp; omega
  rw [htotal] at hcompl; unfold hiddenBitCount; omega

/-- hiddenBitCount m < 2^m for m ≥ 2.
    thm:fold-top-two-zeckendorf-trisect -/
theorem hiddenBitCount_lt_pow (m : Nat) (_hm : 2 ≤ m) :
    hiddenBitCount m < 2 ^ m := by
  have h := paper_hiddenBitCount_closed m
  -- 3 * A(m) + δ = 2^m where δ ≥ 1, so 3 * A(m) < 2^m, so A(m) < 2^m
  split_ifs at h with heven <;> omega

/-- hiddenBitCount m > 0 for m ≥ 2.
    thm:fold-top-two-zeckendorf-trisect -/
theorem hiddenBitCount_pos (m : Nat) (hm : 2 ≤ m) :
    0 < hiddenBitCount m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [hiddenBitCount_recurrence]; positivity

-- ══════════════════════════════════════════════════════════════
-- Phase R20: Right-resolving property
-- ══════════════════════════════════════════════════════════════

/-- Fold is right-resolving: appending different bits always yields different stable words.
    thm:pom-right-resolving -/
theorem Fold_snoc_false_ne_snoc_true (w : Word m) :
    Fold (snoc w false) ≠ Fold (snoc w true) := by
  intro heq
  -- Use stableValue injectivity: if Fold equal, stableValues equal
  have hsv_eq : stableValue (Fold (snoc w false)) = stableValue (Fold (snoc w true)) := by
    rw [heq]
  rw [stableValue_Fold_snoc_false, stableValue_Fold_snoc_true] at hsv_eq
  -- hsv_eq: weight w % F_{m+3} = (weight w + F_{m+2}) % F_{m+3}
  have hF2_lt : Nat.fib (m + 2) < Nat.fib (m + 3) := fib_lt_fib_succ m
  have hF2_pos : 0 < Nat.fib (m + 2) := fib_succ_pos (m + 1)
  have hF3_pos : 0 < Nat.fib (m + 3) := fib_succ_pos (m + 2)
  -- Reduce (weight w + F_{m+2}) % F to (a + F_{m+2}) % F using Nat.add_mod
  have hred : (weight w + Nat.fib (m + 2)) % Nat.fib (m + 3) =
      (weight w % Nat.fib (m + 3) + Nat.fib (m + 2) % Nat.fib (m + 3)) % Nat.fib (m + 3) :=
    Nat.add_mod _ _ _
  rw [Nat.mod_eq_of_lt hF2_lt] at hred
  -- hred: (weight w + F_{m+2}) % F = (a + F_{m+2}) % F where a = weight w % F
  set a := weight w % Nat.fib (m + 3) with ha_def
  rw [hred] at hsv_eq
  -- hsv_eq: a = (a + F_{m+2}) % F_{m+3}
  have ha_lt : a < Nat.fib (m + 3) := Nat.mod_lt _ hF3_pos
  by_cases hle : a + Nat.fib (m + 2) < Nat.fib (m + 3)
  · rw [Nat.mod_eq_of_lt hle] at hsv_eq; omega
  · push_neg at hle
    have : (a + Nat.fib (m + 2)) % Nat.fib (m + 3) =
        a + Nat.fib (m + 2) - Nat.fib (m + 3) := by
      conv_lhs => rw [show a + Nat.fib (m + 2) =
        (a + Nat.fib (m + 2) - Nat.fib (m + 3)) + Nat.fib (m + 3) from by omega]
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [this] at hsv_eq; omega

-- ══════════════════════════════════════════════════════════════
-- Phase R21: Bit-resolving and left-resolving
-- ══════════════════════════════════════════════════════════════

/-- Flipping any single bit changes the Fold image: right-resolving at arbitrary position.
    thm:pom-right-resolving -/
theorem Fold_ne_of_bit_flip {m : Nat} (w : Word m) (i : Fin m) :
    Fold (Function.update w i false) ≠ Fold (Function.update w i true) := by
  intro heq
  -- Key: weight(update w i true) = weight(update w i false) + F_{i+2}
  -- because update (update w i false) i true = update w i true, and bit i is false in update w i false
  have hi_false : Function.update w i false i = false := Function.update_self i false w
  have hweight : weight (Function.update w i true) =
      weight (Function.update w i false) + Nat.fib (i.val + 2) := by
    have : Function.update (Function.update w i false) i true = Function.update w i true := by
      ext j; by_cases hj : j = i
      · subst hj; simp [Function.update_self]
      · simp [Function.update_of_ne hj]
    rw [← this]
    exact weight_update_true_add (Function.update w i false) i hi_false
  -- From Fold_eq_iff_weight_mod: weights are congruent mod F_{m+2}
  rw [Fold_eq_iff_weight_mod] at heq
  -- heq: weight(update w i false) % F_{m+2} = weight(update w i true) % F_{m+2}
  -- So F_{i+2} ≡ 0 (mod F_{m+2}), but 0 < F_{i+2} ≤ F_{m+1} < F_{m+2}
  have hFi_pos : 0 < Nat.fib (i.val + 2) := fib_succ_pos (i.val + 1)
  have hFi_lt : Nat.fib (i.val + 2) < Nat.fib (m + 2) := by
    apply Nat.fib_lt_fib_succ (by omega : 2 ≤ i.val + 2) |>.trans_le
    exact Nat.fib_mono (by omega : i.val + 2 + 1 ≤ m + 2)
  have hFm_pos : 0 < Nat.fib (m + 2) := fib_succ_pos (m + 1)
  -- From heq and hweight: a % F = (a + F_{i+2}) % F where a = weight(update w i false), F = F_{m+2}
  set a := weight (Function.update w i false)
  rw [hweight] at heq
  -- heq: a % F_{m+2} = (a + F_{i+2}) % F_{m+2}
  -- Same modular arithmetic as Fold_snoc_false_ne_snoc_true
  have hred : (a + Nat.fib (i.val + 2)) % Nat.fib (m + 2) =
      (a % Nat.fib (m + 2) + Nat.fib (i.val + 2) % Nat.fib (m + 2)) % Nat.fib (m + 2) :=
    Nat.add_mod _ _ _
  rw [Nat.mod_eq_of_lt hFi_lt] at hred
  set b := a % Nat.fib (m + 2) with hb_def
  rw [hred] at heq
  have hb_lt : b < Nat.fib (m + 2) := Nat.mod_lt _ hFm_pos
  by_cases hle : b + Nat.fib (i.val + 2) < Nat.fib (m + 2)
  · rw [Nat.mod_eq_of_lt hle] at heq; omega
  · push_neg at hle
    have : (b + Nat.fib (i.val + 2)) % Nat.fib (m + 2) =
        b + Nat.fib (i.val + 2) - Nat.fib (m + 2) := by
      conv_lhs => rw [show b + Nat.fib (i.val + 2) =
        (b + Nat.fib (i.val + 2) - Nat.fib (m + 2)) + Nat.fib (m + 2) from by omega]
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [this] at heq; omega

/-- Left-resolving: flipping the first bit changes Fold. Specialization of Fold_ne_of_bit_flip.
    thm:pom-left-resolving -/
theorem Fold_ne_of_first_bit_flip {m : Nat} (w : Word m) (hm : 2 ≤ m) :
    Fold (Function.update w ⟨0, by omega⟩ false) ≠
    Fold (Function.update w ⟨0, by omega⟩ true) :=
  Fold_ne_of_bit_flip w ⟨0, by omega⟩

/-- Paper-facing left-resolving wrapper.
    thm:pom-left-resolving -/
theorem paper_pom_left_resolving {m : Nat} (w : Word m) (hm : 2 ≤ m) :
    Fold (Function.update w ⟨0, by omega⟩ false) ≠
    Fold (Function.update w ⟨0, by omega⟩ true) :=
  Fold_ne_of_first_bit_flip w hm

-- ══════════════════════════════════════════════════════════════
-- Phase R29: hiddenBitCount density bound
-- ══════════════════════════════════════════════════════════════

/-- hiddenBitCount is approximately 2^m / 3: 3B ≤ 2^m ≤ 3B + 2.
    thm:pom-hidden-bit-density -/
theorem hiddenBitCount_near_third (m : Nat) :
    3 * hiddenBitCount m ≤ 2 ^ m ∧ 2 ^ m ≤ 3 * hiddenBitCount m + 2 := by
  have h := paper_hiddenBitCount_closed m
  split_ifs at h with heven <;> omega

/-- Hidden bit is 0 when the last position is false: weight < threshold.
    lem:pom-hidden-bit-last-false -/
theorem hiddenBit_last_false (w : Word (m + 1))
    (hLast : w ⟨m, Nat.lt_succ_self m⟩ = false) :
    hiddenBit w = 0 := by
  unfold hiddenBit
  simp only [show m + 1 + 2 = m + 3 from by omega]
  rw [if_neg]
  intro h
  have hwt := weight_of_lastFalse hLast
  have hlt := X.weight_lt_fib (truncate w)
  omega

/-- Hidden bit is 1 when both last and penultimate are true.
    lem:pom-hidden-bit-boolean-recurrence-true -/
theorem hiddenBit_boolean_recurrence (w : Word (m + 3))
    (hLast : w ⟨m + 2, by omega⟩ = true)
    (hPenult : w ⟨m + 1, by omega⟩ = true) :
    hiddenBit w = 1 := by
  unfold hiddenBit
  rw [if_pos]
  -- weight w = weight(truncate w) + F(m+4)
  have hw := weight_of_lastTrue (m := m + 2) hLast
  have hPenult' : (truncate w) ⟨m + 1, by omega⟩ = true := by
    show w ⟨m + 1, by omega⟩ = true; exact hPenult
  have hw2 := weight_of_lastTrue (m := m + 1) (by convert hPenult')
  have hfib := Omega.fib_succ_succ' (m + 3)
  simp only [show m + 2 + 2 = m + 4 from by omega, show m + 1 + 2 = m + 3 from by omega,
    show m + 3 + 2 = m + 5 from by omega] at hw hw2 hfib ⊢
  omega

/-- Hidden bit recurrence when last is true and penultimate is false:
    hiddenBit w = hiddenBit (truncate (truncate w)).
    lem:pom-hidden-bit-boolean-recurrence-false -/
theorem hiddenBit_boolean_recurrence_false (w : Word (m + 3))
    (hLast : w ⟨m + 2, by omega⟩ = true)
    (hPenult : w ⟨m + 1, by omega⟩ = false) :
    hiddenBit w = hiddenBit (truncate (truncate w)) := by
  unfold hiddenBit
  -- weight w = weight(truncate w) + F(m+4)
  have hw := weight_of_lastTrue (m := m + 2) hLast
  -- weight(truncate w) = weight(truncate² w) since penultimate is false
  have hPenult' : (truncate w) ⟨m + 1, by omega⟩ = false := by
    show w ⟨m + 1, by omega⟩ = false; exact hPenult
  have hw2 := weight_of_lastFalse (m := m + 1) (by convert hPenult')
  have hfib := Omega.fib_succ_succ' (m + 3)
  simp only [show m + 2 + 2 = m + 4 from by omega, show m + 1 + 2 = m + 3 from by omega,
    show m + 3 + 2 = m + 5 from by omega] at hw hw2 hfib ⊢
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; omega
  · exfalso; omega
  · rfl

-- ══════════════════════════════════════════════════════════════
-- Phase R68: Unified hiddenBit Boolean recurrence
-- ══════════════════════════════════════════════════════════════

/-- Unified Boolean recurrence for hiddenBit on Word(m+3).
    If last=false: hiddenBit = 0.
    If last=true, penult=true: hiddenBit = 1.
    If last=true, penult=false: hiddenBit = hiddenBit(truncate²).
    thm:pom-hidden-bit-unified-recurrence -/
theorem hiddenBit_unified_recurrence (w : Word (m + 3))
    (hLast : w ⟨m + 2, by omega⟩ = true) :
    hiddenBit w = if w ⟨m + 1, by omega⟩ = true then 1
      else hiddenBit (truncate (truncate w)) := by
  cases hPenult : w ⟨m + 1, by omega⟩
  · -- penultimate = false
    simp only [Bool.false_eq_true, ite_false]
    exact hiddenBit_boolean_recurrence_false w hLast hPenult
  · -- penultimate = true
    simp only [ite_true]
    exact hiddenBit_boolean_recurrence w hLast hPenult

-- ══════════════════════════════════════════════════════════════
-- Phase R69: hiddenBitCount = 2^m / 3 (Nat floor division)
-- ══════════════════════════════════════════════════════════════

private theorem two_pow_mod_three : ∀ m : Nat,
    2 ^ m % 3 = if m % 2 = 0 then 1 else 2
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
    have ih := two_pow_mod_three m
    have h4 : 2 ^ (m + 2) = 4 * 2 ^ m := by ring
    have hmod : (m + 2) % 2 = m % 2 := by omega
    rw [h4, hmod]
    -- 4 * 2^m mod 3 = (4 mod 3) * (2^m mod 3) mod 3 = 1 * (2^m mod 3) mod 3 = 2^m mod 3
    have : (4 * 2 ^ m) % 3 = (4 % 3 * (2 ^ m % 3)) % 3 := Nat.mul_mod 4 (2 ^ m) 3
    rw [this, show 4 % 3 = 1 from rfl, one_mul, Nat.mod_mod_of_dvd]
    · exact ih
    · decide

/-- hiddenBitCount m = ⌊2^m / 3⌋.
    thm:pom-hidden-bit-count-floor-div -/
theorem hiddenBitCount_floor_div_three (m : Nat) :
    hiddenBitCount m = 2 ^ m / 3 := by
  have hclosed := paper_hiddenBitCount_closed m
  have hmod := two_pow_mod_three m
  split_ifs at hclosed hmod with heven <;> omega

-- ══════════════════════════════════════════════════════════════
-- Phase R323: hiddenBitCount double-index closed forms
-- ══════════════════════════════════════════════════════════════

/-- Closed form for hiddenBitCount at even indices: 3·B(2m) + 1 = 4^m.
    thm:pom-hidden-bit-count -/
theorem hiddenBitCount_double_closed (m : Nat) :
    3 * hiddenBitCount (2 * m) + 1 = 4 ^ m := by
  match m with
  | 0 => simp [hiddenBitCount_zero]
  | m + 1 =>
    have h := hiddenBitCount_even_closed (m + 1) (by omega)
    have hpos : 1 ≤ 4 ^ (m + 1) := Nat.one_le_pow _ _ (by omega)
    omega

private theorem four_pow_mod_three (m : Nat) : 4 ^ m % 3 = 1 := by
  induction m with
  | zero => simp
  | succ n ih =>
    have : 4 ^ (n + 1) = 4 * 4 ^ n := by ring
    rw [this]; omega

/-- hiddenBitCount at even indices via floor division.
    thm:pom-hidden-bit-count -/
theorem hiddenBitCount_double_eq (m : Nat) :
    hiddenBitCount (2 * m) = (4 ^ m - 1) / 3 := by
  have hclosed := hiddenBitCount_double_closed m
  have hmod := four_pow_mod_three m
  omega

/-- hiddenBitCount is monotone.
    thm:pom-hidden-bit-count -/
theorem hiddenBitCount_le_succ (m : Nat) :
    hiddenBitCount m ≤ hiddenBitCount (m + 1) := by
  simp only [hiddenBitCount_floor_div_three]
  exact Nat.div_le_div_right (Nat.pow_le_pow_right (by omega) (by omega))

/-- Successor relation: B(m+1) = 2·B(m) + m % 2.
    thm:pom-hidden-bit-count -/
theorem hiddenBitCount_succ_eq (m : Nat) :
    hiddenBitCount (m + 1) = 2 * hiddenBitCount m + m % 2 := by
  simp only [hiddenBitCount_floor_div_three, show 2 ^ (m + 1) = 2 * 2 ^ m from by ring]
  have hmod := two_pow_mod_three m
  by_cases hm : m % 2 = 0
  · rw [hm] at hmod; simp at hmod; omega
  · have hm1 : m % 2 = 1 := by omega
    rw [hm1] at hmod; simp at hmod; omega

/-- Complement relation: 2^m - B(m) = 2·B(m) + δ where δ ∈ {1,2}.
    thm:pom-hidden-bit-count -/
theorem hiddenBitCount_complement (m : Nat) :
    2 ^ m - hiddenBitCount m = 2 * hiddenBitCount m + (if m % 2 = 0 then 1 else 2) := by
  have := hiddenBitCount_closed m; omega

/-- hiddenBitCount mod 2 parity: B(m+2) % 2 = (m+1) % 2.
    thm:pom-hidden-bit-count -/
theorem hiddenBitCount_mod2 (m : Nat) :
    hiddenBitCount (m + 2) % 2 = (m + 1) % 2 := by
  rw [hiddenBitCount_succ_eq (m + 1), hiddenBitCount_succ_eq m]
  omega

/-- B(m+2) % 2 = B(m) % 2 for m ≥ 1.
    thm:pom-hidden-bit-count -/
theorem hiddenBitCount_add_two_mod2 (m : Nat) (hm : 1 ≤ m) :
    hiddenBitCount (m + 2) % 2 = hiddenBitCount m % 2 := by
  rw [hiddenBitCount_recurrence]
  have h2m : 2 ∣ 2 ^ m := by
    exact dvd_pow_self 2 (by omega : m ≠ 0)
  omega

/-- B(m) + B(m+1) = 2^m - 1.
    thm:pom-hidden-bit-count -/
theorem hiddenBitCount_add_succ_eq (m : Nat) :
    hiddenBitCount m + hiddenBitCount (m + 1) = 2 ^ m - 1 := by
  have h1 := hiddenBitCount_closed m
  have h2 := hiddenBitCount_closed (m + 1)
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  rw [hpow] at h2
  split_ifs at h1 h2 with hm hm1 <;> omega

/-- Closed form: 3·B(2m+1) + 2 = 2·4^m.
    thm:pom-hidden-bit-count -/
theorem hiddenBitCount_odd_closed_eq (m : Nat) :
    3 * hiddenBitCount (2 * m + 1) + 2 = 2 * 4 ^ m := by
  have := hiddenBitCount_odd_closed m
  have hpos : 2 ≤ 2 * 4 ^ m := by
    have := Nat.one_le_pow m 4 (by omega)
    omega
  omega

private theorem two_four_pow_mod_three (m : Nat) : (2 * 4 ^ m) % 3 = 2 := by
  induction m with
  | zero => simp
  | succ n ih =>
    have : 2 * 4 ^ (n + 1) = 4 * (2 * 4 ^ n) := by ring
    rw [this]; omega

/-- hiddenBitCount at odd indices via floor division.
    thm:pom-hidden-bit-count -/
theorem hiddenBitCount_odd_eq (m : Nat) :
    hiddenBitCount (2 * m + 1) = (2 * 4 ^ m - 2) / 3 := by
  have hclosed := hiddenBitCount_odd_closed_eq m
  have hmod := two_four_pow_mod_three m
  omega

/-- Fold is canonical (value-preserving), idempotent, and surjective.
    prop:fold-basic-paper -/
theorem paper_fold_basic (m : Nat) :
    (∀ w : Word m, Fold (Fold w).1 = Fold w) ∧
    (Function.Surjective (Fold (m := m))) ∧
    (∀ w : Word m, stableValue (Fold w) = weight w % Nat.fib (m + 2)) :=
  ⟨fun w => Fold_idempotent w, Fold_surjective m, fun w => stableValue_Fold_mod w⟩

/-- Hidden bit count extended values m=13..16.
    thm:pom-hidden-bit-count -/
theorem paper_hiddenBitCount_extended_values :
    hiddenBitCount 13 = 2730 ∧
    hiddenBitCount 14 = 5461 ∧
    hiddenBitCount 15 = 10922 ∧
    hiddenBitCount 16 = 21845 := by
  simp only [hiddenBitCount_floor_div_three]; omega

/-- Hidden bit stability and threshold properties.
    lem:pom-one-bit + thm:pom-hidden-bit-count -/
theorem paper_hiddenBit_stable_and_threshold :
    (∀ (m : Nat) (w : Word m), hiddenBit w = 1 ↔ Nat.fib (m + 2) ≤ weight w) ∧
    3 * hiddenBitCount 6 = 2 ^ 6 - 1 ∧
    3 * hiddenBitCount 7 = 2 ^ 7 - 2 := by
  refine ⟨fun m w => ?_, ?_, ?_⟩
  · simp only [hiddenBit]; split <;> omega
  · have := hiddenBitCount_even_closed 3 (by omega); omega
  · have := hiddenBitCount_odd_closed 3; omega

/-- Paper package: right-resolving separation at the final snoc bit.
    This is the paper-facing wrapper for the final-bit distinguishability lemma.
    prop:pom-right-resolving-package -/
theorem paper_pom_right_resolving_package (w : Omega.Word m) :
    Omega.Fold (Omega.snoc w false) ≠ Omega.Fold (Omega.snoc w true) :=
  Omega.Fold_snoc_false_ne_snoc_true w
