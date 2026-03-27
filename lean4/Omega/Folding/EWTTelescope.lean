import Omega.Folding.MomentTriple

namespace Omega

-- ══════════════════════════════════════════════════════════════
-- Phase 150: EWT telescope via Word³ exact triple collision
-- ══════════════════════════════════════════════════════════════

/-- EWT(m) = |{(w1,w2,w3) : Word m³ | weight w1 = weight w2 = weight w3}|.
    bridge:ewt-triple-exact -/
theorem exactWeightTriple_eq_triple_exact (m : Nat) :
    exactWeightTriple m =
    (Finset.univ.filter (fun p : Word m × Word m × Word m =>
      weight p.1 = weight p.2.1 ∧ weight p.2.1 = weight p.2.2)).card := by
  classical
  simp only [exactWeightTriple, exactWeightCount]
  simp_rw [show ∀ n, (Finset.univ.filter (fun w : Word m => weight w = n)).card ^ 3 =
    ((Finset.univ.filter (fun w : Word m => weight w = n)) ×ˢ
     ((Finset.univ.filter (fun w : Word m => weight w = n)) ×ˢ
      (Finset.univ.filter (fun w : Word m => weight w = n)))).card from
    fun n => by simp [Finset.card_product]; ring]
  rw [← Finset.card_biUnion]
  · congr 1; ext ⟨w1, w2, w3⟩
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_product,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨n, _, hw1, hw2, hw3⟩; exact ⟨hw1.trans hw2.symm, hw2.trans hw3.symm⟩
    · intro ⟨h12, h23⟩
      exact ⟨weight w1, X.weight_lt_fib w1, rfl, h12.symm, (h12.trans h23).symm⟩
  · intro n _ n' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro ⟨w1, _, _⟩ ⟨hw1, _⟩ ⟨hw1', _⟩
    exact hne (hw1.symm.trans hw1')

-- ══════════════════════════════════════════════════════════════
-- Exact triple collision class
-- ══════════════════════════════════════════════════════════════

/-- Exact triple collision class for given last-bit pattern.
    bridge:ewt-class-def -/
def exactTripleCollisionClass (m : Nat) (b1 b2 b3 : Bool) : Finset (Word m × Word m × Word m) :=
  Finset.univ.filter (fun p : Word m × Word m × Word m =>
    weight p.1 + (if b1 then Nat.fib (m + 2) else 0) =
    weight p.2.1 + (if b2 then Nat.fib (m + 2) else 0) ∧
    weight p.2.1 + (if b2 then Nat.fib (m + 2) else 0) =
    weight p.2.2 + (if b3 then Nat.fib (m + 2) else 0))

set_option maxHeartbeats 400000 in
/-- Each last-bit slice at level m+1 bijects to an exactTripleCollisionClass at level m.
    bridge:ewt-class-card -/
private theorem exactTripleClass_card_eq (m : Nat) (b1 b2 b3 : Bool) :
    (Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) × Word (m + 1) =>
      weight p.1 = weight p.2.1 ∧ weight p.2.1 = weight p.2.2 ∧
      p.1 ⟨m, by omega⟩ = b1 ∧ p.2.1 ⟨m, by omega⟩ = b2 ∧ p.2.2 ⟨m, by omega⟩ = b3)).card =
    (exactTripleCollisionClass m b1 b2 b3).card := by
  unfold exactTripleCollisionClass
  apply Finset.card_bij
    (fun (p : Word (m + 1) × Word (m + 1) × Word (m + 1)) _ =>
      (truncate p.1, truncate p.2.1, truncate p.2.2))
  · intro ⟨w1, w2, w3⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    constructor
    · have := hp.1; rw [weight, hp.2.2.1, weight, hp.2.2.2.1] at this; exact this
    · have := hp.2.1; rw [weight, hp.2.2.2.1, weight, hp.2.2.2.2] at this; exact this
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

/-- EWT(m+1) = sum of 8 exact triple collision classes.
    bridge:ewt-8-split -/
theorem exactWeightTriple_lastBit_split (m : Nat) :
    exactWeightTriple (m + 1) =
    (exactTripleCollisionClass m false false false).card +
    (exactTripleCollisionClass m false false true).card +
    (exactTripleCollisionClass m false true false).card +
    (exactTripleCollisionClass m false true true).card +
    (exactTripleCollisionClass m true false false).card +
    (exactTripleCollisionClass m true false true).card +
    (exactTripleCollisionClass m true true false).card +
    (exactTripleCollisionClass m true true true).card := by
  classical
  rw [exactWeightTriple_eq_triple_exact]
  set T := Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) × Word (m + 1) =>
    weight p.1 = weight p.2.1 ∧ weight p.2.1 = weight p.2.2)
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
  simp only [Fintype.sum_prod_type, Fintype.univ_bool,
    Finset.sum_insert (by decide : true ∉ ({false} : Finset Bool)),
    Finset.sum_singleton]
  have hf : ∀ b1 b2 b3 : Bool,
      (T.filter (fun p => lastBits p = (b1, b2, b3))).card =
      (Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) × Word (m + 1) =>
        weight p.1 = weight p.2.1 ∧ weight p.2.1 = weight p.2.2 ∧
        p.1 ⟨m, by omega⟩ = b1 ∧ p.2.1 ⟨m, by omega⟩ = b2 ∧
        p.2.2 ⟨m, by omega⟩ = b3)).card := by
    intro b1 b2 b3; congr 1; ext ⟨w1, w2, w3⟩
    simp only [T, lastBits, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    tauto
  have h := exactTripleClass_card_eq m
  simp only [hf, h]; omega

-- ══════════════════════════════════════════════════════════════
-- Orbit identification
-- ══════════════════════════════════════════════════════════════

/-- exactTripleCollisionClass(fff) = exactWeightTriple.
    bridge:ewt-fff -/
theorem exactTripleClass_fff (m : Nat) :
    (exactTripleCollisionClass m false false false).card = exactWeightTriple m := by
  rw [exactWeightTriple_eq_triple_exact]; rfl

/-- exactTripleCollisionClass(ttt) = exactWeightTriple.
    bridge:ewt-ttt -/
theorem exactTripleClass_ttt (m : Nat) :
    (exactTripleCollisionClass m true true true).card = exactWeightTriple m := by
  rw [exactWeightTriple_eq_triple_exact]; congr 1; ext ⟨w1, w2, w3⟩
  simp only [exactTripleCollisionClass, Finset.mem_filter, Finset.mem_univ, true_and, ite_true]
  constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> omega

-- ══════════════════════════════════════════════════════════════
-- Phase 151: permutation symmetry + orbit identification + final merge
-- ══════════════════════════════════════════════════════════════

/-- Swap positions 1↔2 preserves collision class card.
    bridge:ewt-swap12 -/
theorem exactTripleClass_swap12 (m : Nat) (b1 b2 b3 : Bool) :
    (exactTripleCollisionClass m b1 b2 b3).card =
    (exactTripleCollisionClass m b2 b1 b3).card := by
  apply Finset.card_bij (fun p _ => (p.2.1, p.1, p.2.2))
  · intro ⟨w1, w2, w3⟩ hp
    simp only [exactTripleCollisionClass, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.1.symm, hp.1.trans hp.2⟩
  · intro ⟨a1, a2, a3⟩ _ ⟨b1', b2', b3'⟩ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)
  · intro ⟨w1, w2, w3⟩ hw
    simp only [exactTripleCollisionClass, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact ⟨(w2, w1, w3), ⟨hw.1.symm, hw.1.trans hw.2⟩, rfl⟩

/-- Swap positions 2↔3 preserves collision class card.
    bridge:ewt-swap23 -/
theorem exactTripleClass_swap23 (m : Nat) (b1 b2 b3 : Bool) :
    (exactTripleCollisionClass m b1 b2 b3).card =
    (exactTripleCollisionClass m b1 b3 b2).card := by
  apply Finset.card_bij (fun p _ => (p.1, p.2.2, p.2.1))
  · intro ⟨w1, w2, w3⟩ hp
    simp only [exactTripleCollisionClass, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    constructor
    · exact hp.1.trans hp.2
    · exact hp.2.symm
  · intro ⟨a1, a2, a3⟩ _ ⟨b1', b2', b3'⟩ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.2 h.2.1)
  · intro ⟨w1, w2, w3⟩ hw
    simp only [exactTripleCollisionClass, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact ⟨(w1, w3, w2), ⟨hw.1.trans hw.2, hw.2.symm⟩, rfl⟩

/-- {fft} class = CCSL: Σ_n ewc(n) · ewc(n+F)².
    bridge:ewt-fft-ccsl -/
theorem exactTripleClass_fft_eq_ccsl (m : Nat) :
    (exactTripleCollisionClass m false false true).card = crossCorrSqLow m := by
  classical
  -- fft: wt(v1) = wt(v2), wt(v2) = wt(v3) + F
  -- Group by n = wt(v3): v1,v2 have weight n+F, v3 has weight n
  simp only [crossCorrSqLow, exactWeightCount]
  -- Need: |{(v1,v2,v3) : fft condition}| = Σ_n |{w:wt=n}| · |{w:wt=n+F}|²
  -- RHS = Σ_n |{w:wt=n+F}|² · |{w:wt=n}| = Σ_n |{w:wt=n+F} ×ˢ ({w:wt=n+F} ×ˢ {w:wt=n})|
  simp_rw [show ∀ n, (Finset.univ.filter (fun w : Word m => weight w = n)).card *
    (Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 2))).card ^ 2 =
    ((Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 2))) ×ˢ
     ((Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 2))) ×ˢ
      (Finset.univ.filter (fun w : Word m => weight w = n)))).card from
    fun n => by simp [Finset.card_product]; ring]
  rw [← Finset.card_biUnion]
  · congr 1; ext ⟨v1, v2, v3⟩
    simp only [exactTripleCollisionClass, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.false_eq_true, ite_false, Nat.add_zero, ite_true]
    constructor
    · intro ⟨h12, h2F⟩
      exact ⟨weight v3, X.weight_lt_fib v3, by omega, by omega, rfl⟩
    · rintro ⟨n, _, hw1, hw2, hw3⟩; exact ⟨by omega, by omega⟩
  · intro n _ n' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro ⟨_, _, v3⟩ ⟨_, _, hw3⟩ ⟨_, _, hw3'⟩
    exact hne (hw3.symm.trans hw3')

/-- {ftt} class = CCSH: Σ_n ewc(n)² · ewc(n+F).
    bridge:ewt-ftt-ccsh -/
theorem exactTripleClass_ftt_eq_ccsh (m : Nat) :
    (exactTripleCollisionClass m false true true).card = crossCorrSqHigh m := by
  classical
  -- ftt: wt(v1) = wt(v2) + F, wt(v2) = wt(v3)
  -- Group by n = wt(v2) = wt(v3): v1 has weight n+F
  simp only [crossCorrSqHigh, exactWeightCount]
  simp_rw [show ∀ n, (Finset.univ.filter (fun w : Word m => weight w = n)).card ^ 2 *
    (Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 2))).card =
    ((Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 2))) ×ˢ
     ((Finset.univ.filter (fun w : Word m => weight w = n)) ×ˢ
      (Finset.univ.filter (fun w : Word m => weight w = n)))).card from
    fun n => by simp [Finset.card_product]; ring]
  rw [← Finset.card_biUnion]
  · congr 1; ext ⟨v1, v2, v3⟩
    simp only [exactTripleCollisionClass, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.false_eq_true, ite_false, Nat.add_zero, ite_true]
    constructor
    · intro ⟨h1F, h23⟩
      exact ⟨weight v2, X.weight_lt_fib v2, by omega, rfl, by omega⟩
    · rintro ⟨n, _, hw1, hw2, hw3⟩; exact ⟨by omega, by omega⟩
  · intro n _ n' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro ⟨_, v2, _⟩ ⟨_, hw2, _⟩ ⟨_, hw2', _⟩
    exact hne (hw2.symm.trans hw2')

/-- EWT(m+1) = 2·EWT(m) + 3·CCSH(m) + 3·CCSL(m).
    prop:pom-s3-recurrence -/
theorem exactWeightTriple_succ (m : Nat) :
    exactWeightTriple (m + 1) = 2 * exactWeightTriple m +
    3 * crossCorrSqHigh m + 3 * crossCorrSqLow m := by
  rw [exactWeightTriple_lastBit_split, exactTripleClass_fff, exactTripleClass_ttt]
  -- {fft,ftf,tff} → 3·CCSL
  rw [exactTripleClass_fft_eq_ccsl]
  rw [show (exactTripleCollisionClass m false true false).card = crossCorrSqLow m from by
    rw [← exactTripleClass_swap23 m false false true]; exact exactTripleClass_fft_eq_ccsl m]
  rw [show (exactTripleCollisionClass m true false false).card = crossCorrSqLow m from by
    rw [← exactTripleClass_swap12 m false true false, ← exactTripleClass_swap23 m false false true]
    exact exactTripleClass_fft_eq_ccsl m]
  -- {ftt,tft,ttf} → 3·CCSH
  rw [exactTripleClass_ftt_eq_ccsh]
  rw [show (exactTripleCollisionClass m true false true).card = crossCorrSqHigh m from by
    rw [← exactTripleClass_swap12 m false true true]; exact exactTripleClass_ftt_eq_ccsh m]
  rw [show (exactTripleCollisionClass m true true false).card = crossCorrSqHigh m from by
    rw [← exactTripleClass_swap23 m true false true, ← exactTripleClass_swap12 m false true true]
    exact exactTripleClass_ftt_eq_ccsh m]
  ring

end Omega
