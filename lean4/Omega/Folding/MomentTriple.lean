import Omega.Folding.MomentRecurrence
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace Omega

-- ══════════════════════════════════════════════════════════════
-- S_3(m+1) last-bit split into 8 collision classes
-- ══════════════════════════════════════════════════════════════

/-- Helper: triple collision class for given bit offsets. -/
def tripleCollisionClass (m : Nat) (b1 b2 b3 : Bool) : Finset (Word m × Word m × Word m) :=
  Finset.univ.filter (fun p : Word m × Word m × Word m =>
    (weight p.1 + if b1 then Nat.fib (m + 2) else 0) % Nat.fib (m + 3) =
    (weight p.2.1 + if b2 then Nat.fib (m + 2) else 0) % Nat.fib (m + 3) ∧
    (weight p.2.1 + if b2 then Nat.fib (m + 2) else 0) % Nat.fib (m + 3) =
    (weight p.2.2 + if b3 then Nat.fib (m + 2) else 0) % Nat.fib (m + 3))

set_option maxHeartbeats 400000 in
/-- Each last-bit slice at level m+1 bijects to a tripleCollisionClass at level m. -/
private theorem tripleClass_card_eq (m : Nat) (b1 b2 b3 : Bool) :
    (Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) × Word (m + 1) =>
      weight p.1 % Nat.fib (m + 3) = weight p.2.1 % Nat.fib (m + 3) ∧
      weight p.2.1 % Nat.fib (m + 3) = weight p.2.2 % Nat.fib (m + 3) ∧
      p.1 ⟨m, by omega⟩ = b1 ∧ p.2.1 ⟨m, by omega⟩ = b2 ∧ p.2.2 ⟨m, by omega⟩ = b3)).card =
    (tripleCollisionClass m b1 b2 b3).card := by
  unfold tripleCollisionClass
  apply Finset.card_bij
    (fun (p : Word (m + 1) × Word (m + 1) × Word (m + 1)) _ =>
      (truncate p.1, truncate p.2.1, truncate p.2.2))
  · intro ⟨w1, w2, w3⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [weight, hp.2.2.1, weight, hp.2.2.2.1, weight, hp.2.2.2.2] at hp
    exact ⟨hp.1, hp.2.1⟩
  · intro ⟨w1a, w2a, w3a⟩ ha ⟨w1b, w2b, w3b⟩ hb heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at ha hb heq ⊢
    exact ⟨by rw [← X.snoc_truncate_last w1a, ← X.snoc_truncate_last w1b,
                   heq.1, ha.2.2.1, hb.2.2.1],
           by rw [← X.snoc_truncate_last w2a, ← X.snoc_truncate_last w2b,
                   heq.2.1, ha.2.2.2.1, hb.2.2.2.1],
           by rw [← X.snoc_truncate_last w3a, ← X.snoc_truncate_last w3b,
                   heq.2.2, ha.2.2.2.2, hb.2.2.2.2]⟩
  · intro ⟨v1, v2, v3⟩ hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    refine ⟨(snoc v1 b1, snoc v2 b2, snoc v3 b3), ?_, by simp⟩
    refine ⟨?_, ?_, by simp, by simp, by simp⟩
    · rw [weight_snoc, weight_snoc]; exact hv.1
    · rw [weight_snoc, weight_snoc]; exact hv.2

/-- S_3(m+1) = Σ_{b1,b2,b3} |tripleCollisionClass m b1 b2 b3|.
    prop:pom-s3-recurrence -/
theorem momentSum_three_lastBit_split (m : Nat) :
    momentSum 3 (m + 1) =
    (tripleCollisionClass m false false false).card +
    (tripleCollisionClass m false false true).card +
    (tripleCollisionClass m false true false).card +
    (tripleCollisionClass m false true true).card +
    (tripleCollisionClass m true false false).card +
    (tripleCollisionClass m true false true).card +
    (tripleCollisionClass m true true false).card +
    (tripleCollisionClass m true true true).card := by
  classical
  rw [momentSum_three_eq_triple_collision, triple_collision_iff_weight_mod]
  rw [show Nat.fib ((m + 1) + 2) = Nat.fib (m + 3) from by ring_nf]
  -- Rewrite the full collision set as a disjoint union of 8 slices by last bits
  -- then apply tripleClass_card_eq to each slice.
  -- Total = Σ over all 8 bit-triples of (slice card) = Σ (tripleCollisionClass card)
  -- Strategy: each element belongs to exactly one slice determined by its last bits.
  -- Use: card S = Σ_{b} card(S ∩ {last bits = b})
  -- The key bijection
  have h := tripleClass_card_eq m
  -- Partition the collision set into 8 disjoint parts by last bits
  set T := Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) × Word (m + 1) =>
    weight p.1 % Nat.fib (m + 3) = weight p.2.1 % Nat.fib (m + 3) ∧
    weight p.2.1 % Nat.fib (m + 3) = weight p.2.2 % Nat.fib (m + 3))
  let lastBits : Word (m + 1) × Word (m + 1) × Word (m + 1) → Bool × Bool × Bool :=
    fun p => (p.1 ⟨m, by omega⟩, p.2.1 ⟨m, by omega⟩, p.2.2 ⟨m, by omega⟩)
  have hpartition : T.card =
      ∑ b : Bool × Bool × Bool,
        (T.filter (fun p => lastBits p = b)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext p
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hp => ⟨lastBits p, hp, rfl⟩, fun ⟨_, hp, _⟩ => hp⟩
    · intro b _ b' _ hne
      apply Finset.disjoint_filter.mpr
      intro p _ h1 h2; exact hne (h1.symm.trans h2)
  rw [hpartition]
  -- Expand the sum over Bool × Bool × Bool into 8 explicit terms
  simp only [Fintype.sum_prod_type, Fintype.univ_bool, Finset.sum_insert (by decide : true ∉ ({false} : Finset Bool)),
    Finset.sum_singleton]
  -- Each filter term equals the restricted collision set
  have hf : ∀ b1 b2 b3 : Bool,
      (T.filter (fun p => lastBits p = (b1, b2, b3))).card =
      (Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) × Word (m + 1) =>
        weight p.1 % Nat.fib (m + 3) = weight p.2.1 % Nat.fib (m + 3) ∧
        weight p.2.1 % Nat.fib (m + 3) = weight p.2.2 % Nat.fib (m + 3) ∧
        p.1 ⟨m, by omega⟩ = b1 ∧ p.2.1 ⟨m, by omega⟩ = b2 ∧
        p.2.2 ⟨m, by omega⟩ = b3)).card := by
    intro b1 b2 b3; congr 1; ext ⟨w1, w2, w3⟩
    simp only [T, lastBits, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    tauto
  simp only [hf, h]; omega

-- ══════════════════════════════════════════════════════════════
-- Bit-flip cancellation (Finset equality)
-- ══════════════════════════════════════════════════════════════

/-- T(1,1,1) = T(0,0,0): adding F_{m+2} to all three offsets cancels.
    prop:pom-s3-recurrence -/
theorem tripleCollisionClass_cancel_111 (m : Nat) :
    tripleCollisionClass m true true true = tripleCollisionClass m false false false := by
  unfold tripleCollisionClass; ext ⟨v1, v2, v3⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ↓reduceIte, Nat.add_zero]
  exact ⟨fun ⟨h1, h2⟩ => ⟨Nat.ModEq.add_right_cancel' _ h1, Nat.ModEq.add_right_cancel' _ h2⟩,
         fun ⟨h1, h2⟩ => ⟨Nat.ModEq.add_right _ h1, Nat.ModEq.add_right _ h2⟩⟩

-- ══════════════════════════════════════════════════════════════
-- Permutation symmetries (card equalities via bijection)
-- ══════════════════════════════════════════════════════════════

/-- Swapping (v1,v2,v3) → (v2,v1,v3) sends T(b1,b2,b3).card = T(b2,b1,b3).card.
    prop:pom-s3-recurrence -/
theorem tripleCollisionClass_swap12 (m : Nat) (b1 b2 b3 : Bool) :
    (tripleCollisionClass m b1 b2 b3).card =
    (tripleCollisionClass m b2 b1 b3).card := by
  unfold tripleCollisionClass
  apply Finset.card_bij (fun (p : Word m × Word m × Word m) _ => (p.2.1, p.1, p.2.2))
  · intro ⟨v1, v2, v3⟩ hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨hv.1.symm, hv.1.trans hv.2⟩
  · intro ⟨a1, a2, a3⟩ _ ⟨b1', b2', b3'⟩ _ h
    simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)
  · intro ⟨v1, v2, v3⟩ hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨(v2, v1, v3), ⟨hv.1.symm, hv.1.trans hv.2⟩, rfl⟩

/-- Swapping (v1,v2,v3) → (v1,v3,v2) sends T(b1,b2,b3).card = T(b1,b3,b2).card.
    prop:pom-s3-recurrence -/
theorem tripleCollisionClass_swap23 (m : Nat) (b1 b2 b3 : Bool) :
    (tripleCollisionClass m b1 b2 b3).card =
    (tripleCollisionClass m b1 b3 b2).card := by
  unfold tripleCollisionClass
  apply Finset.card_bij (fun (p : Word m × Word m × Word m) _ => (p.1, p.2.2, p.2.1))
  · intro ⟨v1, v2, v3⟩ hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨hv.1.trans hv.2, hv.2.symm⟩
  · intro ⟨a1, a2, a3⟩ _ ⟨b1', b2', b3'⟩ _ h
    simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 (Prod.ext h.2.2 h.2.1)
  · intro ⟨v1, v2, v3⟩ hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨(v1, v3, v2), ⟨hv.1.trans hv.2, hv.2.symm⟩, rfl⟩

/-- Swapping (v1,v2,v3) → (v3,v2,v1) sends T(b1,b2,b3).card = T(b3,b2,b1).card.
    prop:pom-s3-recurrence -/
theorem tripleCollisionClass_swap13 (m : Nat) (b1 b2 b3 : Bool) :
    (tripleCollisionClass m b1 b2 b3).card =
    (tripleCollisionClass m b3 b2 b1).card := by
  unfold tripleCollisionClass
  apply Finset.card_bij (fun (p : Word m × Word m × Word m) _ => (p.2.2, p.2.1, p.1))
  · intro ⟨v1, v2, v3⟩ hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨hv.2.symm, hv.1.symm⟩
  · intro ⟨a1, a2, a3⟩ _ ⟨b1', b2', b3'⟩ _ h
    simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.2 (Prod.ext h.2.1 h.1)
  · intro ⟨v1, v2, v3⟩ hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨(v3, v2, v1), ⟨hv.2.symm, hv.1.symm⟩, rfl⟩

-- ══════════════════════════════════════════════════════════════
-- S_3(m+1) = 2·T(0,0,0) + 3·T(0,0,1) + 3·T(0,1,1)
-- ══════════════════════════════════════════════════════════════

/-- S_3(m+1) reduces to 3 distinct collision classes via symmetry.
    prop:pom-s3-recurrence -/
theorem momentSum_three_succ_three_term (m : Nat) :
    momentSum 3 (m + 1) =
    2 * (tripleCollisionClass m false false false).card +
    3 * (tripleCollisionClass m false false true).card +
    3 * (tripleCollisionClass m false true true).card := by
  rw [momentSum_three_lastBit_split]
  -- T111 = T000 by Finset equality
  rw [congrArg Finset.card (tripleCollisionClass_cancel_111 m)]
  -- Orbit {T001, T010, T100}: T001 = T010 (swap23), T010 = T100 (swap12)
  have h1 := tripleCollisionClass_swap23 m false false true   -- T001 = T010
  have h2 := tripleCollisionClass_swap12 m false true false   -- T010 = T100
  -- Orbit {T011, T101, T110}: T011 = T101 (swap12), T101 = T110 (swap23)
  have h3 := tripleCollisionClass_swap12 m false true true    -- T011 = T101
  have h4 := tripleCollisionClass_swap23 m true false true    -- T101 = T110
  omega

-- ══════════════════════════════════════════════════════════════
-- E000 = exactWeightTriple (Σ ewc³)
-- ══════════════════════════════════════════════════════════════

/-- T(0,0,0) = Σ_n ewc(m,n)³: all three words share the same weight.
    prop:pom-s3-recurrence -/
theorem tripleCollisionClass_000_eq_ewcCube (m : Nat) :
    (tripleCollisionClass m false false false).card = exactWeightTriple m := by
  classical
  unfold tripleCollisionClass
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  -- Since weight < F_{m+3}, mod is identity
  have hmod : ∀ v : Word m, weight v % Nat.fib (m + 3) = weight v :=
    fun v => Nat.mod_eq_of_lt (X.weight_lt_fib v)
  simp_rw [hmod]
  unfold exactWeightTriple exactWeightCount
  -- Now: |{(v1,v2,v3) : wt v1 = wt v2 ∧ wt v2 = wt v3}| = Σ_n ewc(n)³
  -- ewc(n)³ = |{v1:wt=n}| · |{v2:wt=n}| · |{v3:wt=n}| = |{v1:wt=n} ×ˢ {v2:wt=n} ×ˢ {v3:wt=n}|
  have hprod : ∀ n, (Finset.univ.filter (fun w : Word m => weight w = n)).card ^ 3 =
      ((Finset.univ.filter (fun w : Word m => weight w = n)) ×ˢ
       ((Finset.univ.filter (fun w : Word m => weight w = n)) ×ˢ
        (Finset.univ.filter (fun w : Word m => weight w = n)))).card := by
    intro n; rw [Finset.card_product, Finset.card_product]; ring
  simp_rw [hprod]; symm
  rw [← Finset.card_biUnion]
  · congr 1; ext ⟨v1, v2, v3⟩
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨n, _, h1, h2, h3⟩; exact ⟨h1 ▸ h2 ▸ rfl, h2 ▸ h3 ▸ rfl⟩
    · intro ⟨h12, h23⟩
      exact ⟨weight v1, X.weight_lt_fib v1, rfl, h12.symm, (h12.trans h23).symm⟩
  · intro n _ n' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro ⟨v1, _, _⟩ ⟨h1, _⟩ ⟨h2, _⟩; exact hne (h1.symm.trans h2)

-- ══════════════════════════════════════════════════════════════
-- E001 and E011 in ewc terms (definitions)
-- ══════════════════════════════════════════════════════════════

/-- Triple cross-correlation: Σ ewc(n)^a · ewc(n+d)^b.
    prop:pom-s3-recurrence -/
def tripleCorr (m d : Nat) (a b : Nat) : Nat :=
  ∑ n ∈ Finset.range (Nat.fib (m + 3)),
    exactWeightCount m n ^ a * exactWeightCount m (n + d) ^ b

/-- S_3(m+1) = 2·exactWeightTriple(m) + 3·T001(m) + 3·T011(m).
    prop:pom-s3-recurrence -/
theorem momentSum_three_succ_ewt_form (m : Nat) :
    momentSum 3 (m + 1) =
    2 * exactWeightTriple m +
    3 * (tripleCollisionClass m false false true).card +
    3 * (tripleCollisionClass m false true true).card := by
  rw [momentSum_three_succ_three_term, tripleCollisionClass_000_eq_ewcCube]

-- ══════════════════════════════════════════════════════════════
-- Cross-correlation-squared definitions (CCSH, CCSL)
-- ══════════════════════════════════════════════════════════════

/-- Cross-correlation-squared high: Σ ewc(n)² · ewc(n + F_{m+2}).
    prop:pom-s3-recurrence -/
def crossCorrSqHigh (m : Nat) : Nat :=
  ∑ n ∈ Finset.range (Nat.fib (m + 3)),
    exactWeightCount m n ^ 2 * exactWeightCount m (n + Nat.fib (m + 2))

/-- Cross-correlation-squared low: Σ ewc(n) · ewc(n + F_{m+2})².
    prop:pom-s3-recurrence -/
def crossCorrSqLow (m : Nat) : Nat :=
  ∑ n ∈ Finset.range (Nat.fib (m + 3)),
    exactWeightCount m n * exactWeightCount m (n + Nat.fib (m + 2)) ^ 2

/-- CCSH = tripleCorr specialized to (2,1) at shift F_{m+2}.
    prop:pom-s3-recurrence -/
theorem crossCorrSqHigh_eq_tripleCorr (m : Nat) :
    crossCorrSqHigh m = tripleCorr m (Nat.fib (m + 2)) 2 1 := by
  unfold crossCorrSqHigh tripleCorr; congr 1; ext n; ring

/-- CCSL = tripleCorr specialized to (1,2) at shift F_{m+2}.
    prop:pom-s3-recurrence -/
theorem crossCorrSqLow_eq_tripleCorr (m : Nat) :
    crossCorrSqLow m = tripleCorr m (Nat.fib (m + 2)) 1 2 := by
  unfold crossCorrSqLow tripleCorr; congr 1; ext n; ring


-- ══════════════════════════════════════════════════════════════
-- S_3 bounds
-- ══════════════════════════════════════════════════════════════

/-- S_3(m) ≥ 2^m (generalized from S_q ≥ 2^m for q ≥ 1).
    prop:pom-moment-congruence-q -/
theorem momentSum_three_ge_pow (m : Nat) : 2 ^ m ≤ momentSum 3 m :=
  momentSum_ge_pow' 3 m (by omega)

/-- S_3(m) ≥ S_2(m) (moment monotonicity in q).
    prop:pom-moment-congruence-q -/
theorem momentSum_three_ge_two (m : Nat) : momentSum 2 m ≤ momentSum 3 m :=
  momentSum_le_succ' 2 m

-- ══════════════════════════════════════════════════════════════
-- S_2 difference recurrence
-- ══════════════════════════════════════════════════════════════

/-- S_2 difference recurrence: Δ(m+2) = S_2(m+2) + 2·Δ(m)
    where Δ(k) = S_2(k+1) - S_2(k).
    prop:pom-s2-recurrence -/
theorem momentSum_two_diff_recurrence (m : Nat) :
    momentSum 2 (m + 3) - momentSum 2 (m + 2) =
    momentSum 2 (m + 2) + 2 * (momentSum 2 (m + 1) - momentSum 2 m) := by
  -- From recurrence: S(m+3) + 2S(m) = 2S(m+2) + 2S(m+1)
  -- So S(m+3) - S(m+2) = S(m+2) + 2S(m+1) - 2S(m) - S(m+2)... wait
  -- S(m+3) = 2S(m+2) + 2S(m+1) - 2S(m) [recurrence_sub]
  -- S(m+3) - S(m+2) = S(m+2) + 2S(m+1) - 2S(m)
  -- = S(m+2) + 2(S(m+1) - S(m))
  have hrec := momentSum_two_recurrence m
  have hmono := momentSum_two_mono' m
  omega

/-- S_2 difference sequence is strictly increasing for m ≥ 1.
    prop:pom-s2-recurrence -/
theorem momentSum_two_diff_strict_mono (m : Nat) (hm : 1 ≤ m) :
    momentSum 2 (m + 1) - momentSum 2 m <
    momentSum 2 (m + 2) - momentSum 2 (m + 1) := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => omega
    | 1 => rw [momentSum_two_one, momentSum_two_two, momentSum_two_three]; omega
    | m + 2 =>
      -- Δ(m+3) = S(m+3) + 2·Δ(m+1) [diff_recurrence at m+1]
      -- Δ(m+2) = S(m+2) + 2·Δ(m) [diff_recurrence at m]
      -- Need: Δ(m+2) < Δ(m+3)
      -- Δ(m+3) - Δ(m+2) = (S(m+3) + 2·Δ(m+1)) - (S(m+2) + 2·Δ(m))
      --                   = (S(m+3) - S(m+2)) + 2·(Δ(m+1) - Δ(m))
      -- Wait, that's circular. Let me use the recurrence directly.
      -- Use the additive recurrence directly: S(m+3) + 2S(m) = 2S(m+2) + 2S(m+1)
      have hrec := momentSum_two_recurrence m
      have hrec1 := momentSum_two_recurrence (m + 1)
      -- Monotonicity gives all S values are increasing
      have hm0 := momentSum_two_mono' m
      have hm1 := momentSum_two_mono' (m + 1)
      have hm2 := momentSum_two_mono' (m + 2)
      have hm3 := momentSum_two_mono' (m + 3)
      -- IH: S(m+2)-S(m+1) > S(m+1)-S(m)
      have hih := ih (m + 1) (by omega) (by omega)
      -- S(m+3)-S(m+2) > S(m+2)-S(m+1)
      -- From hrec1: S(m+4) + 2S(m+1) = 2S(m+3) + 2S(m+2)
      -- S(m+4)-S(m+3) = S(m+3) + 2S(m+2) - 2S(m+1) - S(m+3) ... hmm, wrong index
      -- Let me use hrec at m: S(m+3) + 2S(m) = 2S(m+2) + 2S(m+1)
      -- S(m+3) - S(m+2) = S(m+2) + 2S(m+1) - 2S(m) - S(m+2)... no
      -- S(m+3) = 2S(m+2) + 2S(m+1) - 2S(m) [from hrec]
      -- S(m+3) - S(m+2) = S(m+2) + 2(S(m+1) - S(m))
      -- S(m+2) - S(m+1) = S(m+1) + 2(S(m) - S(m-1))... by diff_recurrence at m-1
      -- So S(m+3)-S(m+2) - (S(m+2)-S(m+1)) = S(m+2)-S(m+1) + 2(S(m+1)-S(m)) - 2(S(m)-S(m-1))
      -- Hmm, this uses diff_recurrence at m-1 which we might not have for m+2 case.
      -- Simpler: from the additive recurrence:
      -- Need: S(m+3)-S(m+2) > S(m+2)-S(m+1)
      -- hrec: S(m+3) = 2S(m+2) + 2S(m+1) - 2S(m)
      -- So S(m+3)-S(m+2) = S(m+2) + 2S(m+1) - 2S(m) = S(m+2) + 2(S(m+1)-S(m))
      -- And S(m+2)-S(m+1) is what we compare against.
      -- Need: S(m+2) + 2(S(m+1)-S(m)) > S(m+2)-S(m+1)
      -- i.e., 2(S(m+1)-S(m)) > -(S(m+1))
      -- i.e., 2S(m+1)-2S(m) + S(m+1) > 0
      -- i.e., 3S(m+1) > 2S(m), which follows from S(m+1) ≥ S(m) [mono].
      -- Actually need: 3S(m+1) - 2S(m) > S(m+2) - S(m+1)... wait.
      -- Let me redo. Need: S(m+2)+2(S(m+1)-S(m)) > S(m+2)-S(m+1)
      -- ↔ 2S(m+1)-2S(m) > -S(m+1) ↔ 3S(m+1) > 2S(m)
      -- True since S(m+1) ≥ S(m) implies 3S(m+1) ≥ 3S(m) > 2S(m). ✓
      -- But omega has Nat subtraction issues. Let me restate without subtraction.
      -- Need: S(m+2) + S(m+1) + S(m+3) > 2*S(m+2) + S(m+1)... hmm
      -- Actually the goal IS about Nat subtraction:
      -- S(m+2+1) - S(m+2) > S(m+2) - S(m+1+1)... let me just try linarith
      -- Actually goal with show m+2 = m+2: S(m+3)-S(m+2) > S(m+2)-S(m+1)
      -- i.e., S(m+3) + S(m+1) > 2*S(m+2) [equivalent without subtraction]
      -- From hrec: S(m+3) + 2S(m) = 2S(m+2) + 2S(m+1)
      -- So S(m+3) = 2S(m+2) + 2S(m+1) - 2S(m)
      -- S(m+3) + S(m+1) = 2S(m+2) + 3S(m+1) - 2S(m) > 2S(m+2) [iff 3S(m+1) > 2S(m)]
      -- 3S(m+1) > 2S(m): since S(m+1) ≥ S(m), 3S(m+1) ≥ 3S(m) > 2S(m). ✓
      -- The goal after match m+2 is: S(m+3)-S(m+2) < S(m+4)-S(m+3)
      -- Use recurrence at m+1: S(m+4) + 2S(m+1) = 2S(m+3) + 2S(m+2)
      have hrec1 := momentSum_two_recurrence (m + 1)
      have hmono_m1 := momentSum_two_mono' (m + 1)
      have hmono_m2 := momentSum_two_mono' (m + 2)
      have hmono_m3 := momentSum_two_mono' (m + 3)
      have hpos := momentSum_two_pos' (m + 1)
      -- Additive form: S(m+4) + S(m+2) > 2*S(m+3)
      -- From hrec1: S(m+4) = 2S(m+3) + 2S(m+2) - 2S(m+1)
      -- S(m+4) + S(m+2) = 2S(m+3) + 3S(m+2) - 2S(m+1) > 2S(m+3) iff 3S(m+2) > 2S(m+1)
      have hkey : momentSum 2 (m + 4) + momentSum 2 (m + 2) > 2 * momentSum 2 (m + 3) := by
        linarith
      -- a - b < c - d when a + d < b + c and b ≤ a and d ≤ c
      -- Here a = S(m+3), b = S(m+2), c = S(m+4), d = S(m+3)
      -- a + d = 2S(m+3) < S(m+4) + S(m+2) = b + c [from hkey]
      -- b ≤ a: S(m+2) ≤ S(m+3) [hmono_m2]
      -- d ≤ c: S(m+3) ≤ S(m+4) [hmono_m3]
      -- Convert: S(m+3)-S(m+2) < S(m+4)-S(m+3)
      -- Cast to ℤ where subtraction works
      zify [hmono_m2, hmono_m3]; linarith

/-- S_2(m+2) ≥ S_2(m+1) + S_2(m): Fibonacci-like growth.
    prop:pom-s2-recurrence -/
theorem momentSum_two_fibonacci_growth (m : Nat) :
    momentSum 2 (m + 1) + momentSum 2 m ≤ momentSum 2 (m + 2) := by
  match m with
  | 0 => rw [momentSum_two_zero, momentSum_two_one, momentSum_two_two]; omega
  | 1 => rw [momentSum_two_one, momentSum_two_two, momentSum_two_three]; omega
  | m + 2 =>
    -- From recurrence: S(m+4) + 2S(m+1) = 2S(m+3) + 2S(m+2)
    -- So S(m+4) = 2S(m+3) + 2S(m+2) - 2S(m+1)
    -- Need: S(m+3) + S(m+2) ≤ S(m+4) = 2S(m+3) + 2S(m+2) - 2S(m+1)
    -- i.e., 2S(m+1) ≤ S(m+3) + S(m+2)
    -- True since S(m+1) ≤ S(m+2) ≤ S(m+3).
    have hrec := momentSum_two_recurrence (m + 1)
    have hmono1 := momentSum_two_mono' (m + 1)
    have hmono2 := momentSum_two_mono' (m + 2)
    -- hrec: S(m+4) + 2S(m+1) = 2S(m+3) + 2S(m+2)
    -- Need: S(m+3) + S(m+2) ≤ S(m+4)
    -- i.e., S(m+3) + S(m+2) + 2S(m+1) ≤ S(m+4) + 2S(m+1) = 2S(m+3) + 2S(m+2)
    -- i.e., 2S(m+1) ≤ S(m+3) + S(m+2), true by monotonicity
    linarith

/-- S_2(m)² ≤ F_{m+2} · S_4(m): Cauchy-Schwarz with f = d².
    prop:pom-moment-congruence-q -/
theorem momentSum_two_sq_le_card_mul_four (m : Nat) :
    momentSum 2 m ^ 2 ≤ Nat.fib (m + 2) * momentSum 4 m := by
  -- S_2 = Σ d(x)², S_4 = Σ d(x)⁴, |X_m| = F_{m+2}
  -- By Cauchy-Schwarz: (Σ f(x))² ≤ |X| · Σ f(x)² with f(x) = d(x)²
  rw [← momentSum_zero]
  simp only [momentSum, pow_zero, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [← Finset.card_univ (α := X m)]
  -- (Σ d²)² ≤ |X| · Σ d⁴
  have : (∑ x : X m, X.fiberMultiplicity x ^ 2) ^ 2 ≤
      Finset.univ.card * ∑ x : X m, (X.fiberMultiplicity x ^ 2) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  convert this using 2 with x
  ring

-- ══════════════════════════════════════════════════════════════
-- Phase 123
-- ══════════════════════════════════════════════════════════════

/-- Generalized Cauchy-Schwarz: S_q(m)² ≤ F_{m+2} · S_{2q}(m).
    prop:pom-moment-congruence-q -/
theorem momentSum_cauchy_schwarz_general (q m : Nat) :
    momentSum q m ^ 2 ≤ Nat.fib (m + 2) * momentSum (2 * q) m := by
  rw [← momentSum_zero]
  simp only [momentSum, pow_zero, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [← Finset.card_univ (α := X m)]
  have : (∑ x : X m, X.fiberMultiplicity x ^ q) ^ 2 ≤
      Finset.univ.card * ∑ x : X m, (X.fiberMultiplicity x ^ q) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  simp_rw [show ∀ x : X m, (X.fiberMultiplicity x ^ q) ^ 2 = X.fiberMultiplicity x ^ (2 * q) from
    fun x => by rw [← pow_mul, Nat.mul_comm]] at this
  exact this

/-- ewc(m, 0) = 1 (public alias).
    prop:pom-moment-congruence-q -/
theorem exactWeightCount_zero (m : Nat) : exactWeightCount m 0 = 1 :=
  exactWeightCount_zero_eq_one' m

/-- ewc at max weight = 1 (only all-true has weight F_{m+3}-2).
    prop:pom-moment-congruence-q -/
theorem exactWeightCount_max (m : Nat) :
    exactWeightCount m (Nat.fib (m + 3) - 2) = 1 := by
  have h := exactWeightCount_symmetric m 0 (by omega)
  simp only [Nat.sub_zero] at h
  rw [← h]; exact exactWeightCount_zero m

/-- Fold(complement w) has weight (F_{m+3}-2-weight w) mod F_{m+2}.
    lem:pom-fold-congruence -/
theorem Fold_complement_mod (w : Word m) :
    stableValue (Fold (complement w)) = (Nat.fib (m + 3) - 2 - weight w) % Nat.fib (m + 2) := by
  rw [stableValue_Fold_mod, weight_complement_sub]

/-- ewc(m, 1) = 1 for m ≥ 1: only the word with a single true at position 0 has weight 1.
    prop:pom-moment-congruence-q -/
theorem exactWeightCount_one (m : Nat) (hm : 1 ≤ m) : exactWeightCount m 1 = 1 := by
  induction m with
  | zero => omega
  | succ n ih =>
    -- ewc(n+1, 1) = ewc(n, 1) + (if F_{n+2} ≤ 1 then ewc(n, 1-F) else 0)
    -- F_{n+2} ≥ 1 always, and F_{n+2} ≤ 1 only when n+2 ≤ 2, i.e., n ≤ 0
    rw [exactWeightCount_succ]
    cases n with
    | zero => native_decide
    | succ k =>
      have hFib : ¬(Nat.fib (k + 3) ≤ 1) := by
        have := fib_succ_pos (k + 2)
        have : Nat.fib (k + 3) ≥ 2 := by
          calc Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
            _ ≥ 1 + 1 := Nat.add_le_add (fib_succ_pos k) (fib_succ_pos (k + 1))
        omega
      simp [hFib]
      exact ih (by omega)

/-- The maximum stableValue F_{m+2}-1 is achieved by some stable word.
    thm:finite-resolution-mod -/
theorem stableValue_max_achieved (m : Nat) (hm : 1 ≤ m) :
    ∃ x : X m, stableValue x = Nat.fib (m + 2) - 1 := by
  have hF : 0 < Nat.fib (m + 2) := fib_succ_pos (m + 1)
  obtain ⟨x, hx⟩ := X.stableValueFin_surjective m ⟨Nat.fib (m + 2) - 1, by omega⟩
  exact ⟨x, by simp [X.stableValueFin] at hx; omega⟩

-- ══════════════════════════════════════════════════════════════
-- S_2 high-order values by recurrence
-- ══════════════════════════════════════════════════════════════

/-- prop:pom-s2-recurrence -/
theorem momentSum_two_ten_rec : momentSum 2 10 = 8320 := by
  have h := momentSum_two_recurrence 7
  simp only [show (7 : Nat) + 3 = 10 from rfl, show (7 : Nat) + 2 = 9 from rfl,
    show (7 : Nat) + 1 = 8 from rfl, momentSum_two_seven_rec,
    momentSum_two_eight_rec, momentSum_two_nine_rec] at h; omega

/-- prop:pom-s2-recurrence -/
theorem momentSum_two_eleven_rec : momentSum 2 11 = 20640 := by
  have h := momentSum_two_recurrence 8
  simp only [show (8 : Nat) + 3 = 11 from rfl, show (8 : Nat) + 2 = 10 from rfl,
    show (8 : Nat) + 1 = 9 from rfl, momentSum_two_eight_rec,
    momentSum_two_nine_rec, momentSum_two_ten_rec] at h; omega

/-- prop:pom-s2-recurrence -/
theorem momentSum_two_twelve_rec : momentSum 2 12 = 51216 := by
  have h := momentSum_two_recurrence 9
  simp only [show (9 : Nat) + 3 = 12 from rfl, show (9 : Nat) + 2 = 11 from rfl,
    show (9 : Nat) + 1 = 10 from rfl, momentSum_two_nine_rec,
    momentSum_two_ten_rec, momentSum_two_eleven_rec] at h; omega

-- ══════════════════════════════════════════════════════════════
-- S_2 mod 16 divisibility
-- ══════════════════════════════════════════════════════════════

/-- 16 ∣ S_2(m) for m ≥ 10.
    prop:pom-s2-recurrence -/
theorem momentSum_two_mod_sixteen (m : Nat) (hm : 10 ≤ m) : 16 ∣ momentSum 2 m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => omega
    | 10 => exact ⟨520, by rw [momentSum_two_ten_rec]⟩
    | 11 => exact ⟨1290, by rw [momentSum_two_eleven_rec]⟩
    | 12 => exact ⟨3201, by rw [momentSum_two_twelve_rec]⟩
    | m + 13 =>
      have hrec := momentSum_two_recurrence (m + 10)
      rw [show (m + 10 + 3 : Nat) = m + 13 from rfl,
        show (m + 10 + 2 : Nat) = m + 12 from rfl,
        show (m + 10 + 1 : Nat) = m + 11 from rfl] at hrec
      have h10 := ih (m + 10) (by omega) (by omega)
      have h11 := ih (m + 11) (by omega) (by omega)
      have h12 := ih (m + 12) (by omega) (by omega)
      obtain ⟨a, ha⟩ := h10; obtain ⟨b, hb⟩ := h11; obtain ⟨c, hc⟩ := h12
      rw [ha, hb, hc] at hrec
      have hab : a ≤ b := by
        have := momentSum_two_mono' (m + 10)
        rw [ha, show (m + 10 + 1 : Nat) = m + 11 from rfl, hb] at this; omega
      exact ⟨2 * (c + b) - 2 * a, by omega⟩

-- ══════════════════════════════════════════════════════════════
-- Phase 129
-- ══════════════════════════════════════════════════════════════

/-- E00(m) ≥ F_{m+2}.
    prop:pom-s2-recurrence -/
theorem exactWeightCollision_ge_fib (m : Nat) :
    Nat.fib (m + 2) ≤ exactWeightCollision m := by
  induction m with
  | zero => exact le_of_eq (by native_decide)
  | succ n ih =>
    have hsucc := exactWeightCollision_succ n
    have hge := momentSum_ge_card' 2 n
    have hmono : Nat.fib (n + 1) ≤ Nat.fib (n + 2) := Nat.fib_mono (by omega)
    have hfib : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    calc Nat.fib (n + 1 + 2) = Nat.fib (n + 3) := by rfl
      _ = Nat.fib (n + 1) + Nat.fib (n + 2) := hfib
      _ ≤ momentSum 2 n + Nat.fib (n + 2) := Nat.add_le_add_right (le_trans hmono hge) _
      _ ≤ momentSum 2 n + exactWeightCollision n := Nat.add_le_add_left ih _
      _ = exactWeightCollision n + momentSum 2 n := Nat.add_comm _ _
      _ = exactWeightCollision (n + 1) := hsucc.symm

/-- E00 is strictly monotone.
    prop:pom-s2-recurrence -/
theorem exactWeightCollision_strict_mono (m : Nat) :
    exactWeightCollision m < exactWeightCollision (m + 1) := by
  rw [exactWeightCollision_succ]; exact Nat.lt_add_of_pos_right (momentSum_pos' 2 m)

/-- Complete S_2 value chain for m = 0..12.
    prop:pom-s2-recurrence -/
theorem momentSum_two_chain_extended :
    momentSum 2 0 = 1 ∧ momentSum 2 1 = 2 ∧ momentSum 2 2 = 6 ∧
    momentSum 2 3 = 14 ∧ momentSum 2 4 = 36 ∧ momentSum 2 5 = 88 ∧
    momentSum 2 6 = 220 ∧ momentSum 2 7 = 544 ∧ momentSum 2 8 = 1352 ∧
    momentSum 2 9 = 3352 ∧ momentSum 2 10 = 8320 ∧ momentSum 2 11 = 20640 ∧
    momentSum 2 12 = 51216 :=
  ⟨momentSum_two_zero, momentSum_two_one, momentSum_two_two,
    momentSum_two_three, momentSum_two_four, momentSum_two_five,
    momentSum_two_six, momentSum_two_seven_rec, momentSum_two_eight_rec,
    momentSum_two_nine_rec, momentSum_two_ten_rec, momentSum_two_eleven_rec,
    momentSum_two_twelve_rec⟩


/-- E00(m) ≥ 2^m.
    prop:pom-s2-recurrence -/
theorem exactWeightCollision_ge_pow (m : Nat) : 2 ^ m ≤ exactWeightCollision m := by
  induction m with
  | zero => have := exactWeightCollision_ge_fib 0; simp [Nat.fib] at this; omega
  | succ n ih =>
    rw [exactWeightCollision_succ]
    have hge := momentSum_two_ge_pow n
    calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      _ ≤ exactWeightCollision n + momentSum 2 n := by linarith

/-- S_2 is convex: 2·S_2(m+1) ≤ S_2(m) + S_2(m+2).
    prop:pom-s2-recurrence -/
theorem momentSum_two_convex (m : Nat) :
    2 * momentSum 2 (m + 1) ≤ momentSum 2 m + momentSum 2 (m + 2) := by
  match m with
  | 0 => rw [momentSum_two_zero, momentSum_two_one, momentSum_two_two]; omega
  | 1 => rw [momentSum_two_one, momentSum_two_two, momentSum_two_three]; omega
  | m + 2 =>
    -- From recurrence: S(m+4) + 2S(m+1) = 2S(m+3) + 2S(m+2)
    -- Need: 2S(m+3) ≤ S(m+2) + S(m+4)
    -- S(m+4) = 2S(m+3) + 2S(m+2) - 2S(m+1) [from recurrence at m+1]
    -- S(m+2) + S(m+4) = S(m+2) + 2S(m+3) + 2S(m+2) - 2S(m+1) = 3S(m+2) + 2S(m+3) - 2S(m+1)
    -- Need: 2S(m+3) ≤ 3S(m+2) + 2S(m+3) - 2S(m+1) ↔ 2S(m+1) ≤ 3S(m+2)
    -- True since S(m+1) ≤ S(m+2) [monotonicity].
    have hrec := momentSum_two_recurrence (m + 1)
    have hmono := momentSum_two_mono' (m + 1)
    linarith

/-- EWT(m) ≥ E00(m): Σ ewc³ ≥ Σ ewc².
    prop:pom-s3-recurrence -/
theorem exactWeightTriple_ge_collision (m : Nat) :
    exactWeightCollision m ≤ exactWeightTriple m := by
  unfold exactWeightCollision exactWeightTriple
  apply Finset.sum_le_sum; intro n _
  -- ewc(n)² ≤ ewc(n)³: a² ≤ a³ for all Nat a (0² = 0 ≤ 0; a ≥ 1 → a² ≤ a³)
  by_cases h : exactWeightCount m n = 0
  · simp [h]
  · have hpos : 1 ≤ exactWeightCount m n := by omega
    calc exactWeightCount m n ^ 2
        = exactWeightCount m n ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ exactWeightCount m n ^ 2 * exactWeightCount m n :=
          Nat.mul_le_mul_left _ hpos
      _ = exactWeightCount m n ^ 3 := by ring

/-- prop:pom-s2-recurrence -/
theorem momentSum_two_two_mod_four : momentSum 2 2 % 4 = 2 := by
  rw [momentSum_two_two]

/-- prop:pom-s2-recurrence -/
theorem momentSum_two_three_mod_four : momentSum 2 3 % 4 = 2 := by
  rw [momentSum_two_three]

/-- Paper certificate: S_2 is the unique sequence satisfying the 3rd-order recurrence
    with initial values 1, 2, 6.
    thm:pom-s2-rank-exact -/
theorem paper_s2_unique_three_state_certificate :
    (∀ m, momentSum 2 (m + 3) + 2 * momentSum 2 m =
      2 * momentSum 2 (m + 2) + 2 * momentSum 2 (m + 1)) ∧
    momentSum 2 0 = 1 ∧ momentSum 2 1 = 2 ∧ momentSum 2 2 = 6 ∧
    (∀ f : Nat → Nat, (∀ m, f (m + 3) + 2 * f m = 2 * f (m + 2) + 2 * f (m + 1)) →
      f 0 = 1 → f 1 = 2 → f 2 = 6 → ∀ m, f m = momentSum 2 m) :=
  ⟨momentSum_two_recurrence, momentSum_two_zero, momentSum_two_one, momentSum_two_two,
   @momentSum_two_determined⟩

/-- Paper definition: S_2(m) = Σ d(x)².
    def:pom-s2 -/
theorem paper_def_s2 (m : Nat) :
    momentSum 2 m = ∑ x : X m, (X.fiberMultiplicity x) ^ 2 := rfl

/-- Paper definition: S_3(m) = Σ d(x)³.
    def:pom-s3 -/
theorem paper_def_s3 (m : Nat) :
    momentSum 3 m = ∑ x : X m, (X.fiberMultiplicity x) ^ 3 := rfl

/-- Paper definition: S_q(m) = Σ d(x)^q.
    def:pom-moment-q -/
theorem paper_def_moment_q (q m : Nat) :
    momentSum q m = ∑ x : X m, (X.fiberMultiplicity x) ^ q := rfl

/-- Paper definition: exactWeightCount.
    def:pom-exactWeightCount -/
theorem paper_exactWeightCount_def (m n : Nat) :
    exactWeightCount m n =
    (Finset.univ.filter (fun w : Word m => weight w = n)).card := rfl

/-- wcc(m,r) ≥ ewc(m,r) since wcc = ewc(r) + ewc(r+F).
    prop:pom-moment-congruence-q -/
theorem weightCongruenceCount_ge_ewc (m r : Nat) (hr : r < Nat.fib (m + 2)) :
    exactWeightCount m r ≤ weightCongruenceCount m r := by
  rw [weightCongruenceCount_eq_sum_ewc m r hr]; omega

/-- S_2(m) = 2^m + excess, where excess = Σ d(x)·(d(x)-1).
    prop:pom-s2-recurrence -/
theorem momentSum_two_excess_sum (m : Nat) :
    momentSum 2 m = 2 ^ m + ∑ x : X m, X.fiberMultiplicity x * (X.fiberMultiplicity x - 1) := by
  simp only [momentSum]
  rw [← X.fiberMultiplicity_sum_eq_pow (m := m)]
  -- Σ d² = Σ (d*(d-1) + d) = Σ d*(d-1) + Σ d
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro x _
  -- d² = d*(d-1) + d for d ≥ 1
  have hpos := X.fiberMultiplicity_pos x
  have : X.fiberMultiplicity x ^ 2 = X.fiberMultiplicity x +
      X.fiberMultiplicity x * (X.fiberMultiplicity x - 1) := by
    cases X.fiberMultiplicity x with
    | zero => omega
    | succ n => simp only [Nat.succ_sub_one]; ring
  exact this


-- ══════════════════════════════════════════════════════════════
-- Phase 145: fiber counting + S_2² ≤ 2^m · S_3
-- ══════════════════════════════════════════════════════════════

/-- Fiber counting identity: summing f(Fold w) over all words equals summing d(x)·f(x) over X m.
    Each stable word x has d(x) preimages under Fold, each contributing f(x).
    bridge:fiber-counting-identity -/
theorem sum_word_eq_sum_fiber_mul (f : X m → Nat) :
    ∑ w : Word m, f (Fold w) = ∑ x : X m, X.fiberMultiplicity x * f x := by
  classical
  have hDisjoint : (↑(Finset.univ : Finset (X m)) : Set (X m)).PairwiseDisjoint X.fiber := by
    intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro w hwx hwy
    exact hxy ((X.mem_fiber.1 hwx).symm.trans (X.mem_fiber.1 hwy))
  have hUnion : (Finset.univ : Finset (Word m)) = Finset.univ.biUnion X.fiber := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_biUnion, true_iff]
    exact ⟨Fold w, trivial, X.mem_fiber_Fold w⟩
  -- LHS: ∑ w : Word m, f(Fold w) = ∑ w ∈ univ, f(Fold w)
  change Finset.univ.sum (fun w => f (Fold w)) = _
  rw [hUnion, Finset.sum_biUnion hDisjoint]
  apply Finset.sum_congr rfl; intro x _
  -- Within each fiber: all w satisfy Fold w = x, so f(Fold w) = f(x)
  have : ∀ w ∈ X.fiber x, f (Fold w) = f x :=
    fun w hw => by rw [X.mem_fiber.1 hw]
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, X.fiberMultiplicity]

/-- The q-th power moment over words equals the (q+1)-th moment sum:
    Σ_w d(Fold w)^q = S_{q+1}(m).
    prop:pom-moment-congruence-q -/
theorem sum_word_fiberMult_pow (q m : Nat) :
    ∑ w : Word m, (X.fiberMultiplicity (Fold w)) ^ q = momentSum (q + 1) m := by
  rw [show (fun w : Word m => (X.fiberMultiplicity (Fold w)) ^ q) =
      (fun w => (fun x : X m => X.fiberMultiplicity x ^ q) (Fold w)) from rfl]
  rw [sum_word_eq_sum_fiber_mul (fun x => X.fiberMultiplicity x ^ q)]
  simp only [momentSum]
  apply Finset.sum_congr rfl; intro x _
  rw [show X.fiberMultiplicity x * X.fiberMultiplicity x ^ q =
      X.fiberMultiplicity x ^ (q + 1) from by rw [pow_succ]; ring]

/-- S_2(m)² ≤ 2^m · S_3(m): Cauchy-Schwarz over the word space.
    Apply (Σ f)² ≤ |S|·Σf² with f(w) = d(Fold w), over Word m.
    prop:pom-moment-congruence-q -/
theorem momentSum_two_sq_le_pow_mul_three (m : Nat) :
    momentSum 2 m ^ 2 ≤ 2 ^ m * momentSum 3 m := by
  -- Rewrite in terms of sums over Word m
  rw [← sum_word_fiberMult_pow 1 m, ← sum_word_fiberMult_pow 2 m]
  show (∑ w : Word m, X.fiberMultiplicity (Fold w) ^ 1) ^ 2 ≤
    2 ^ m * ∑ w : Word m, X.fiberMultiplicity (Fold w) ^ 2
  simp only [pow_one]
  rw [show 2 ^ m = Fintype.card (Word m) from
    (by rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin])]
  rw [← Finset.card_univ (α := Word m)]
  exact sq_sum_le_card_mul_sum_sq

/-- Generalized word-space Cauchy-Schwarz: S_q(m)² ≤ 2^m · S_{2q-1}(m) for q ≥ 1.
    Apply (Σ f)² ≤ |S|·Σf² with f(w) = d(Fold w)^(q-1), over Word m.
    prop:pom-moment-congruence-q -/
theorem momentSum_cauchy_schwarz_word (q m : Nat) (hq : 1 ≤ q) :
    momentSum q m ^ 2 ≤ 2 ^ m * momentSum (2 * q - 1) m := by
  -- q = (q-1) + 1 and 2*q - 1 = 2*(q-1) + 1
  have hq2 : 2 * q - 1 = 2 * (q - 1) + 1 := by omega
  conv_lhs => rw [show q = q - 1 + 1 from by omega]
  rw [hq2]
  rw [← sum_word_fiberMult_pow (q - 1) m, ← sum_word_fiberMult_pow (2 * (q - 1)) m]
  show (∑ w : Word m, X.fiberMultiplicity (Fold w) ^ (q - 1)) ^ 2 ≤
    2 ^ m * ∑ w : Word m, X.fiberMultiplicity (Fold w) ^ (2 * (q - 1))
  simp_rw [show ∀ w : Word m, X.fiberMultiplicity (Fold w) ^ (2 * (q - 1)) =
      (X.fiberMultiplicity (Fold w) ^ (q - 1)) ^ 2 from
      fun w => by rw [← pow_mul, Nat.mul_comm]]
  rw [show 2 ^ m = Fintype.card (Word m) from
    (by rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin])]
  rw [← Finset.card_univ (α := Word m)]
  exact sq_sum_le_card_mul_sum_sq

-- ══════════════════════════════════════════════════════════════
-- Phase 147: log-convexity of moment sums
-- ══════════════════════════════════════════════════════════════

/-- Log-convexity: S_{q+1}(m)² ≤ S_q(m) · S_{q+2}(m).
    Even q = 2k: Cauchy-Schwarz (Σ d^k · d^{k+1})² ≤ (Σ d^{2k})(Σ d^{2k+2}) on X m.
    Odd q = 2k+1: same CS but on Word m via fiber counting.
    prop:pom-moment-congruence-q -/
theorem momentSum_log_convex (q m : Nat) :
    momentSum (q + 1) m ^ 2 ≤ momentSum q m * momentSum (q + 2) m := by
  -- Strategy: write S_{q+1} = Σ (d^a · d^b) where a+b = q+1, then apply CS
  -- For even q=2k: a=k, b=k+1 over X m
  -- For odd q=2k+1: a=k, b=k+1 over Word m (using fiber counting)
  rcases Nat.even_or_odd q with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- Even case: q = 2k, so q = k + k
    subst hk
    -- S_{k+k+1} = Σ d^k · d^{k+1}; CS: (Σ fg)² ≤ (Σ f²)(Σ g²)
    simp only [momentSum]
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun x : X m => X.fiberMultiplicity x ^ k)
      (fun x : X m => X.fiberMultiplicity x ^ (k + 1))
    simp only [← pow_mul, ← pow_add] at hCS
    convert hCS using 2 <;> (apply Finset.sum_congr rfl; intro x _; ring)
  · -- Odd case: q = 2k+1
    subst hk
    -- Move to Word space via sum_word_fiberMult_pow
    rw [show 2 * k + 1 + 1 = (2 * k + 1) + 1 from rfl]
    rw [← sum_word_fiberMult_pow (2 * k + 1) m,
        ← sum_word_fiberMult_pow (2 * k) m,
        ← sum_word_fiberMult_pow (2 * k + 2) m]
    -- CS on Word m with f(w) = d^k, g(w) = d^{k+1}
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun w : Word m => X.fiberMultiplicity (Fold w) ^ k)
      (fun w : Word m => X.fiberMultiplicity (Fold w) ^ (k + 1))
    simp only [← pow_mul, ← pow_add] at hCS
    convert hCS using 2 <;> (apply Finset.sum_congr rfl; intro w _; ring)

/-- Ratio monotonicity: S_{q+1}/S_q ≤ S_{q+2}/S_{q+1}, i.e.,
    S_{q+1}·S_{q+1} ≤ S_q·S_{q+2}. Direct corollary of log-convexity.
    prop:pom-moment-congruence-q -/
theorem momentSum_ratio_mono (q m : Nat) :
    momentSum (q + 1) m * momentSum (q + 1) m ≤
    momentSum q m * momentSum (q + 2) m := by
  have := momentSum_log_convex q m; rwa [sq] at this

-- ══════════════════════════════════════════════════════════════
-- R63: S₂(13), penultimate exactWeightCount, Cauchy 4^m form
-- ══════════════════════════════════════════════════════════════

/-- S₂(13) = 127072, computed via the three-step recurrence from S₂(10..12).
    prop:pom-moment-s2-thirteen -/
theorem momentSum_two_thirteen_rec : momentSum 2 13 = 127072 := by
  have h := momentSum_two_recurrence 10
  rw [show (10 : Nat) + 1 = 11 from rfl, show (10 : Nat) + 2 = 12 from rfl,
    show (10 : Nat) + 3 = 13 from rfl, momentSum_two_ten_rec,
    momentSum_two_eleven_rec, momentSum_two_twelve_rec] at h; omega

/-- The penultimate weight F_{m+3}−3 has exactly one word, by symmetry with weight 1.
    prop:pom-ewc-penultimate -/
theorem exactWeightCount_max_minus_one (m : Nat) (hm : 1 ≤ m) :
    exactWeightCount m (Nat.fib (m + 3) - 3) = 1 := by
  have hfib : Nat.fib (m + 3) ≥ 3 := by
    calc Nat.fib (m + 3) ≥ Nat.fib 4 := Nat.fib_mono (by omega)
      _ = 3 := by native_decide
  have hsub : Nat.fib (m + 3) - 2 - (Nat.fib (m + 3) - 3) = 1 := by omega
  rw [exactWeightCount_symmetric m (Nat.fib (m + 3) - 3) (by omega), hsub]
  exact exactWeightCount_one m hm

/-- Cauchy–Schwarz in 4^m form: 4^m ≤ F_{m+2} · S₂(m).
    prop:pom-moment-cauchy-four -/
theorem momentSum_two_cauchy_lower (m : Nat) :
    4 ^ m ≤ Nat.fib (m + 2) * momentSum 2 m := by
  have h := momentSum_cauchy_schwarz m
  have : (2 ^ m) ^ 2 = 4 ^ m := by
    rw [← pow_mul, show m * 2 = 2 * m from by omega, pow_mul]
    norm_num
  linarith

/-- S₂(14) = 315296, computed via the three-step recurrence from S₂(11..13).
    prop:pom-moment-s2-fourteen -/
theorem momentSum_two_fourteen_rec : momentSum 2 14 = 315296 := by
  have h := momentSum_two_recurrence 11
  rw [show (11 : Nat) + 1 = 12 from rfl, show (11 : Nat) + 2 = 13 from rfl,
    show (11 : Nat) + 3 = 14 from rfl, momentSum_two_eleven_rec,
    momentSum_two_twelve_rec, momentSum_two_thirteen_rec] at h; omega

/-- Weight 2 is achieved by exactly one word for m ≥ 2.
    prop:pom-ewc-weight-two -/
theorem exactWeightCount_two (m : Nat) (hm : 2 ≤ m) :
    exactWeightCount m 2 = 1 := by
  induction m with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => omega
    | succ k =>
      cases k with
      | zero =>
        -- base case: m = 2
        native_decide
      | succ j =>
        -- inductive step: ewc(j+3, 2) = ewc(j+2, 2) since 2 < fib(j+4)
        rw [exactWeightCount_succ_of_lt]
        · exact ih (by omega)
        · -- 2 < Nat.fib (j + 4)
          calc 2 < 3 := by omega
            _ = Nat.fib 4 := by native_decide
            _ ≤ Nat.fib (j + 4) := Nat.fib_mono (by omega)

/-- The weight F_{m+3}−4 has exactly one word, by symmetry with weight 2.
    prop:pom-ewc-fib-sub-four -/
theorem exactWeightCount_fib_sub_four (m : Nat) (hm : 2 ≤ m) :
    exactWeightCount m (Nat.fib (m + 3) - 4) = 1 := by
  have hfib : Nat.fib (m + 3) ≥ 5 := by
    calc Nat.fib (m + 3) ≥ Nat.fib 5 := Nat.fib_mono (by omega)
      _ = 5 := by native_decide
  have hsub : Nat.fib (m + 3) - 2 - (Nat.fib (m + 3) - 4) = 2 := by omega
  rw [exactWeightCount_symmetric m (Nat.fib (m + 3) - 4) (by omega), hsub]
  exact exactWeightCount_two m hm

/-- Weight 3 is achieved by exactly two words for m ≥ 3 (representations: fib(4) and fib(2)+fib(3)).
    prop:pom-ewc-weight-three -/
theorem exactWeightCount_three (m : Nat) (hm : 3 ≤ m) :
    exactWeightCount m 3 = 2 := by
  induction m with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => omega
    | succ k =>
      cases k with
      | zero => omega
      | succ j =>
        cases j with
        | zero =>
          -- base case: m = 3
          native_decide
        | succ i =>
          -- inductive step: ewc(i+4, 3) = ewc(i+3, 3) since 3 < fib(i+5)
          rw [exactWeightCount_succ_of_lt]
          · exact ih (by omega)
          · calc 3 < 5 := by omega
              _ = Nat.fib 5 := by native_decide
              _ ≤ Nat.fib (i + 5) := Nat.fib_mono (by omega)

/-- The weight F_{m+3}−5 has exactly two words, by symmetry with weight 3.
    prop:pom-ewc-fib-sub-five -/
theorem exactWeightCount_fib_sub_five (m : Nat) (hm : 3 ≤ m) :
    exactWeightCount m (Nat.fib (m + 3) - 5) = 2 := by
  have hfib : Nat.fib (m + 3) ≥ 8 := by
    calc Nat.fib (m + 3) ≥ Nat.fib 6 := Nat.fib_mono (by omega)
      _ = 8 := by native_decide
  have hsub : Nat.fib (m + 3) - 2 - (Nat.fib (m + 3) - 5) = 3 := by omega
  rw [exactWeightCount_symmetric m (Nat.fib (m + 3) - 5) (by omega), hsub]
  exact exactWeightCount_three m hm

end Omega
