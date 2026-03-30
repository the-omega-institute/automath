import Omega.Folding.CCSPrimeTelescope

namespace Omega

-- ══════════════════════════════════════════════════════════════
-- Phase 162b: 8-split CCS' telescope + EWT rec + S_3 rec
-- ══════════════════════════════════════════════════════════════

def sClassH (m : Nat) (b1 b2 b3 : Bool) : Finset (Word m × Word m × Word m) :=
  Finset.univ.filter fun p =>
    weight p.1 + (if b1 then Nat.fib (m + 2) else 0) =
      weight p.2.1 + (if b2 then Nat.fib (m + 2) else 0) ∧
    weight p.2.2 + (if b3 then Nat.fib (m + 2) else 0) =
      weight p.1 + (if b1 then Nat.fib (m + 2) else 0) + Nat.fib (m + 2)

def sClassL (m : Nat) (b1 b2 b3 : Bool) : Finset (Word m × Word m × Word m) :=
  Finset.univ.filter fun p =>
    weight p.1 + (if b1 then Nat.fib (m + 2) else 0) + Nat.fib (m + 2) =
      weight p.2.1 + (if b2 then Nat.fib (m + 2) else 0) ∧
    weight p.2.1 + (if b2 then Nat.fib (m + 2) else 0) =
      weight p.2.2 + (if b3 then Nat.fib (m + 2) else 0)

-- ═══ Bijections ═══

set_option maxHeartbeats 400000 in
private theorem sClassH_bij (m : Nat) (b1 b2 b3 : Bool) :
    (Finset.univ.filter fun p : Word (m + 1) × Word (m + 1) × Word (m + 1) =>
      weight p.1 = weight p.2.1 ∧ weight p.2.2 = weight p.1 + Nat.fib (m + 2) ∧
      p.1 ⟨m, by omega⟩ = b1 ∧ p.2.1 ⟨m, by omega⟩ = b2 ∧
      p.2.2 ⟨m, by omega⟩ = b3).card = (sClassH m b1 b2 b3).card := by
  unfold sClassH
  apply Finset.card_bij (fun p _ => (truncate p.1, truncate p.2.1, truncate p.2.2))
  · intro ⟨w1, w2, w3⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have d1 : weight w1 = weight (truncate w1) +
        (if w1 ⟨m, Nat.lt_succ_self m⟩ then Nat.fib (m + 2) else 0) := rfl
    have d2 : weight w2 = weight (truncate w2) +
        (if w2 ⟨m, Nat.lt_succ_self m⟩ then Nat.fib (m + 2) else 0) := rfl
    have d3 : weight w3 = weight (truncate w3) +
        (if w3 ⟨m, Nat.lt_succ_self m⟩ then Nat.fib (m + 2) else 0) := rfl
    rw [hp.2.2.1] at d1; rw [hp.2.2.2.1] at d2; rw [hp.2.2.2.2] at d3
    constructor <;> omega
  · intro ⟨a1, a2, a3⟩ ha ⟨c1, c2, c3⟩ hc heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at ha hc heq ⊢
    exact ⟨by rw [← X.snoc_truncate_last a1, ← X.snoc_truncate_last c1,
                   heq.1, ha.2.2.1, hc.2.2.1],
           by rw [← X.snoc_truncate_last a2, ← X.snoc_truncate_last c2,
                   heq.2.1, ha.2.2.2.1, hc.2.2.2.1],
           by rw [← X.snoc_truncate_last a3, ← X.snoc_truncate_last c3,
                   heq.2.2, ha.2.2.2.2, hc.2.2.2.2]⟩
  · intro ⟨v1, v2, v3⟩ hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨(snoc v1 b1, snoc v2 b2, snoc v3 b3),
      ⟨by rw [weight_snoc, weight_snoc]; exact hv.1,
       by rw [weight_snoc, weight_snoc]; exact hv.2,
       by simp, by simp, by simp⟩, by simp⟩

set_option maxHeartbeats 400000 in
private theorem sClassL_bij (m : Nat) (b1 b2 b3 : Bool) :
    (Finset.univ.filter fun p : Word (m + 1) × Word (m + 1) × Word (m + 1) =>
      weight p.1 + Nat.fib (m + 2) = weight p.2.1 ∧ weight p.2.1 = weight p.2.2 ∧
      p.1 ⟨m, by omega⟩ = b1 ∧ p.2.1 ⟨m, by omega⟩ = b2 ∧
      p.2.2 ⟨m, by omega⟩ = b3).card = (sClassL m b1 b2 b3).card := by
  unfold sClassL
  apply Finset.card_bij (fun p _ => (truncate p.1, truncate p.2.1, truncate p.2.2))
  · intro ⟨w1, w2, w3⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have d1 : weight w1 = weight (truncate w1) +
        (if w1 ⟨m, Nat.lt_succ_self m⟩ then Nat.fib (m + 2) else 0) := rfl
    have d2 : weight w2 = weight (truncate w2) +
        (if w2 ⟨m, Nat.lt_succ_self m⟩ then Nat.fib (m + 2) else 0) := rfl
    have d3 : weight w3 = weight (truncate w3) +
        (if w3 ⟨m, Nat.lt_succ_self m⟩ then Nat.fib (m + 2) else 0) := rfl
    rw [hp.2.2.1] at d1; rw [hp.2.2.2.1] at d2; rw [hp.2.2.2.2] at d3
    constructor <;> omega
  · intro ⟨a1, a2, a3⟩ ha ⟨c1, c2, c3⟩ hc heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at ha hc heq ⊢
    exact ⟨by rw [← X.snoc_truncate_last a1, ← X.snoc_truncate_last c1,
                   heq.1, ha.2.2.1, hc.2.2.1],
           by rw [← X.snoc_truncate_last a2, ← X.snoc_truncate_last c2,
                   heq.2.1, ha.2.2.2.1, hc.2.2.2.1],
           by rw [← X.snoc_truncate_last a3, ← X.snoc_truncate_last c3,
                   heq.2.2, ha.2.2.2.2, hc.2.2.2.2]⟩
  · intro ⟨v1, v2, v3⟩ hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨(snoc v1 b1, snoc v2 b2, snoc v3 b3),
      ⟨by rw [weight_snoc, weight_snoc]; exact hv.1,
       by rw [weight_snoc, weight_snoc]; exact hv.2,
       by simp, by simp, by simp⟩, by simp⟩

-- ═══ Partitions ═══

private theorem splitH (m : Nat) :
    (Finset.univ.filter fun p : Word (m + 1) × Word (m + 1) × Word (m + 1) =>
      weight p.1 = weight p.2.1 ∧ weight p.2.2 = weight p.1 + Nat.fib (m + 2)).card =
    ∑ b : Bool × Bool × Bool, (sClassH m b.1 b.2.1 b.2.2).card := by
  classical
  set T := Finset.univ.filter fun p : Word (m + 1) × Word (m + 1) × Word (m + 1) =>
    weight p.1 = weight p.2.1 ∧ weight p.2.2 = weight p.1 + Nat.fib (m + 2)
  let lb := fun (p : Word (m + 1) × Word (m + 1) × Word (m + 1)) =>
    (p.1 ⟨m, by omega⟩, p.2.1 ⟨m, by omega⟩, p.2.2 ⟨m, by omega⟩)
  rw [show T.card = ∑ b : Bool × Bool × Bool, (T.filter (lb · = b)).card from by
    rw [← Finset.card_biUnion (fun b _ b' _ h => Finset.disjoint_filter.mpr
      fun p _ h1 h2 => h (h1.symm.trans h2))]
    congr 1; ext p; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hp => ⟨lb p, hp, rfl⟩, fun ⟨_, hp, _⟩ => hp⟩]
  congr 1; ext ⟨b1, b2, b3⟩
  rw [show (T.filter (lb · = (b1, b2, b3))).card =
      (Finset.univ.filter fun p : Word (m + 1) × Word (m + 1) × Word (m + 1) =>
        weight p.1 = weight p.2.1 ∧ weight p.2.2 = weight p.1 + Nat.fib (m + 2) ∧
        p.1 ⟨m, by omega⟩ = b1 ∧ p.2.1 ⟨m, by omega⟩ = b2 ∧ p.2.2 ⟨m, by omega⟩ = b3).card from by
    congr 1; ext ⟨w1, w2, w3⟩; simp only [T, lb, Finset.mem_filter, Finset.mem_univ,
      true_and, Prod.mk.injEq]; tauto]
  exact sClassH_bij m b1 b2 b3

private theorem splitL (m : Nat) :
    (Finset.univ.filter fun p : Word (m + 1) × Word (m + 1) × Word (m + 1) =>
      weight p.1 + Nat.fib (m + 2) = weight p.2.1 ∧ weight p.2.1 = weight p.2.2).card =
    ∑ b : Bool × Bool × Bool, (sClassL m b.1 b.2.1 b.2.2).card := by
  classical
  set T := Finset.univ.filter fun p : Word (m + 1) × Word (m + 1) × Word (m + 1) =>
    weight p.1 + Nat.fib (m + 2) = weight p.2.1 ∧ weight p.2.1 = weight p.2.2
  let lb := fun (p : Word (m + 1) × Word (m + 1) × Word (m + 1)) =>
    (p.1 ⟨m, by omega⟩, p.2.1 ⟨m, by omega⟩, p.2.2 ⟨m, by omega⟩)
  rw [show T.card = ∑ b : Bool × Bool × Bool, (T.filter (lb · = b)).card from by
    rw [← Finset.card_biUnion (fun b _ b' _ h => Finset.disjoint_filter.mpr
      fun p _ h1 h2 => h (h1.symm.trans h2))]
    congr 1; ext p; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hp => ⟨lb p, hp, rfl⟩, fun ⟨_, hp, _⟩ => hp⟩]
  congr 1; ext ⟨b1, b2, b3⟩
  rw [show (T.filter (lb · = (b1, b2, b3))).card =
      (Finset.univ.filter fun p : Word (m + 1) × Word (m + 1) × Word (m + 1) =>
        weight p.1 + Nat.fib (m + 2) = weight p.2.1 ∧ weight p.2.1 = weight p.2.2 ∧
        p.1 ⟨m, by omega⟩ = b1 ∧ p.2.1 ⟨m, by omega⟩ = b2 ∧ p.2.2 ⟨m, by omega⟩ = b3).card from by
    congr 1; ext ⟨w1, w2, w3⟩; simp only [T, lb, Finset.mem_filter, Finset.mem_univ,
      true_and, Prod.mk.injEq]; tauto]
  exact sClassL_bij m b1 b2 b3

-- ═══ Orbit identification (simplified: use Finset.ext + omega) ═══

-- H(fft) = EWT, H(ttt) = CCSH via Finset.ext
private theorem hfft (m : Nat) : (sClassH m false false true).card = exactWeightTriple m := by
  rw [exactWeightTriple_eq_triple_exact]; congr 1; ext ⟨v1, v2, v3⟩
  simp only [sClassH, Finset.mem_filter, Finset.mem_univ, true_and,
    Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
  constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> omega

private theorem hfff (m : Nat) : (sClassH m false false false).card = crossCorrSqHigh m := by
  -- fff: wt1=wt2, wt3=wt1+F → ewc(n)²·ewc(n+F) = CCSH
  classical
  simp only [crossCorrSqHigh, exactWeightCount]
  simp_rw [show ∀ n, (Finset.univ.filter (fun w : Word m => weight w = n)).card ^ 2 *
    (Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 2))).card =
    ((Finset.univ.filter (fun w : Word m => weight w = n)) ×ˢ
     ((Finset.univ.filter (fun w : Word m => weight w = n)) ×ˢ
      (Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 2))))).card from
    fun n => by rw [Finset.card_product, Finset.card_product]; ring]
  rw [← Finset.card_biUnion]
  · congr 1; ext ⟨v1, v2, v3⟩
    simp only [sClassH, Finset.mem_biUnion, Finset.mem_range, Finset.mem_product,
      Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.false_eq_true, ite_false, Nat.add_zero]
    exact ⟨fun ⟨h1, h2⟩ => ⟨weight v1, X.weight_lt_fib v1, rfl, h1.symm, by linarith⟩,
      fun ⟨n, _, hw1, hw2, hw3⟩ => ⟨by linarith, by linarith⟩⟩
  · intro n _ n' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro ⟨v1, _, _⟩ ⟨hw1, _⟩ ⟨hw1', _⟩; exact hne (hw1.symm.trans hw1')

private theorem httt (m : Nat) : (sClassH m true true true).card = crossCorrSqHigh m := by
  rw [← hfff]; congr 1; ext ⟨v1, v2, v3⟩
  simp only [sClassH, Finset.mem_filter, Finset.mem_univ, true_and, ite_true, ite_false,
    Nat.add_zero]; constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> omega

-- H(ftt) = CCSL: wt1=wt2+F, wt3+F=wt1+F → wt1=wt2+F, wt3=wt1.
-- Group by n=wt2: ewc(n)·ewc(n+F)² = CCSL
private theorem hftt (m : Nat) : (sClassH m false true true).card = crossCorrSqLow m := by
  classical
  simp only [crossCorrSqLow, exactWeightCount]
  -- v1 has wt n+F, v2 has wt n, v3 has wt n+F. Product: filter(n+F) ×ˢ (filter(n) ×ˢ filter(n+F))
  simp_rw [show ∀ n, (Finset.univ.filter (fun w : Word m => weight w = n)).card *
    (Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 2))).card ^ 2 =
    ((Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 2))) ×ˢ
     ((Finset.univ.filter (fun w : Word m => weight w = n)) ×ˢ
      (Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 2))))).card from
    fun n => by rw [Finset.card_product, Finset.card_product]; ring]
  rw [← Finset.card_biUnion]
  · congr 1; ext ⟨v1, v2, v3⟩
    simp only [sClassH, Finset.mem_biUnion, Finset.mem_range, Finset.mem_product,
      Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
    exact ⟨fun ⟨h1, h2⟩ => ⟨weight v2, X.weight_lt_fib v2, by linarith, rfl, by linarith⟩,
      fun ⟨n, _, hw1, hw2, hw3⟩ => ⟨by linarith, by linarith⟩⟩
  · intro n _ n' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro ⟨v1, v2, _⟩ ⟨_, hw2, _⟩ ⟨_, hw2', _⟩; exact hne (hw2.symm.trans hw2')

-- H(tft) = CCSL: wt1+F=wt2, wt3+F=wt1+2F → wt2=wt1+F, wt3=wt1+F=wt2.
-- Group by n=wt1: ewc(n)·ewc(n+F)² = CCSL
private theorem htft (m : Nat) : (sClassH m true false true).card = crossCorrSqLow m := by
  classical
  simp only [crossCorrSqLow, exactWeightCount]
  simp_rw [show ∀ n, (Finset.univ.filter (fun w : Word m => weight w = n)).card *
    (Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 2))).card ^ 2 =
    ((Finset.univ.filter (fun w : Word m => weight w = n)) ×ˢ
     ((Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 2))) ×ˢ
      (Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 2))))).card from
    fun n => by rw [Finset.card_product, Finset.card_product]; ring]
  rw [← Finset.card_biUnion]
  · congr 1; ext ⟨v1, v2, v3⟩
    simp only [sClassH, Finset.mem_biUnion, Finset.mem_range, Finset.mem_product,
      Finset.mem_filter, Finset.mem_univ, true_and,
      eq_self_iff_true, Bool.false_eq_true, ite_true, ite_false, Nat.add_zero]
    exact ⟨fun ⟨h1, h2⟩ => ⟨weight v1, X.weight_lt_fib v1, rfl, by linarith, by linarith⟩,
      fun ⟨n, _, hw1, hw2, hw3⟩ => ⟨by linarith, by linarith⟩⟩
  · intro n _ n' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro ⟨v1, _, _⟩ ⟨hw1, _⟩ ⟨hw1', _⟩; exact hne (hw1.symm.trans hw1')

-- Empty H classes
private theorem hftf (m : Nat) : (sClassH m false true false).card = 0 := by
  simp only [sClassH, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ⟨v1, v2, v3⟩ _ ⟨h1, h2⟩
  simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at h1 h2
  have := X.weight_lt_fib v3; have : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) :=
    Nat.fib_add_two; have := Nat.fib_mono (show m + 1 ≤ m + 2 from by omega); linarith

private theorem htff (m : Nat) : (sClassH m true false false).card = 0 := by
  simp only [sClassH, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ⟨v1, v2, v3⟩ _ ⟨h1, h2⟩
  simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at h1 h2
  have := X.weight_lt_fib v3; have : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) :=
    Nat.fib_add_two; have := Nat.fib_mono (show m + 1 ≤ m + 2 from by omega); linarith

private theorem httf (m : Nat) : (sClassH m true true false).card = 0 := by
  simp only [sClassH, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ⟨v1, v2, v3⟩ _ ⟨h1, h2⟩
  simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at h1 h2
  have := X.weight_lt_fib v3; have : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) :=
    Nat.fib_add_two; have := Nat.fib_mono (show m + 1 ≤ m + 2 from by omega); linarith

-- L orbits via Finset.ext
private theorem lfff (m : Nat) : (sClassL m false false false).card = crossCorrSqLow m := by
  -- fff: wt1+F=wt2, wt2=wt3 → bijection (v1,v2,v3)↦(v2,v3,v1) to eTC(fft)
  rw [← exactTripleClass_fft_eq_ccsl]
  apply Finset.card_bij (fun p _ => (p.2.1, p.2.2, p.1))
  · intro ⟨v1, v2, v3⟩ hv
    simp only [sClassL, exactTripleCollisionClass, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.false_eq_true, eq_self_iff_true, ite_false, ite_true, Nat.add_zero] at hv ⊢
    constructor <;> linarith
  · intro ⟨a1, a2, a3⟩ _ ⟨c1, c2, c3⟩ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2.2 (Prod.ext h.1 h.2.1)
  · intro ⟨v1, v2, v3⟩ hv
    simp only [sClassL, exactTripleCollisionClass, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.false_eq_true, eq_self_iff_true, ite_false, ite_true, Nat.add_zero] at hv ⊢
    exact ⟨(v3, v1, v2), ⟨by linarith, by linarith⟩, rfl⟩

private theorem lfft (m : Nat) : (sClassL m false false true).card = crossCorrSqHigh m := by
  -- fft: wt1+F=wt2, wt2=wt3+F → wt1=wt3, wt2=wt1+F → CCSH
  -- Biject to exactTripleCollisionClass(ftt) via (v1,v2,v3)↦(v2,v1,v3): eTC(ftt) has wt1=wt2+F, wt2=wt3
  -- After swap: wt1'=wt2=wt1+F, wt2'=wt1=wt3, wt3'=wt3=wt1
  -- eTC(ftt): wt1'+0 = wt2'+F ∧ wt2'+F = wt3'+F → wt1'=wt2'+F ∧ wt2'=wt3'
  -- → wt2=wt1+F ∧ wt1=wt3 ✓
  rw [← exactTripleClass_ftt_eq_ccsh]
  apply Finset.card_bij (fun p _ => (p.2.1, p.1, p.2.2))
  · intro ⟨v1, v2, v3⟩ hv
    simp only [sClassL, exactTripleCollisionClass, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.false_eq_true, eq_self_iff_true, ite_false, ite_true, Nat.add_zero] at hv ⊢
    constructor <;> linarith
  · intro ⟨a1, a2, a3⟩ _ ⟨c1, c2, c3⟩ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)
  · intro ⟨v1, v2, v3⟩ hv
    simp only [sClassL, exactTripleCollisionClass, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.false_eq_true, eq_self_iff_true, ite_false, ite_true, Nat.add_zero] at hv ⊢
    exact ⟨(v2, v1, v3), ⟨by linarith, by linarith⟩, rfl⟩

private theorem lftf (m : Nat) : (sClassL m false true false).card = crossCorrSqHigh m := by
  -- ftf: wt1+F=wt2+F, wt2+F=wt3 → wt1=wt2, wt3=wt1+F → CCSH
  rw [← exactTripleClass_ftt_eq_ccsh]
  -- eTC(fft): wt1=wt2, wt2=wt3+F. After (v1,v2,v3)↦(v3,v2,v1):
  -- wt3=wt2, wt2=wt1+F → same as our lftf? wt1=wt2 and wt3=wt1+F?
  -- No: eTC(fft) after swap gives wt3'=wt2', wt2'=wt1'+F
  -- = wt(v3)=wt(v2), wt(v2)=wt(v1)+F. In lftf we have wt(v1)=wt(v2), wt(v3)=wt(v1)+F.
  -- These have the same structure! Biject via identity.
  -- Actually both say: two equal weights, one weight = those + F.
  -- lftf: v1=v2 weight, v3 = v1+F. eTC(fft) after 1↔3 swap: v3=v2 weight, v2=v1+F → v3=v2, v1=v3+F
  -- lftf: wt1=wt2, wt3=wt1+F. Bijection to eTC(ftt) via (v1,v2,v3)↦(v3,v2,v1)
  apply Finset.card_bij (fun p _ => (p.2.2, p.2.1, p.1))
  · intro ⟨v1, v2, v3⟩ hv
    simp only [sClassL, exactTripleCollisionClass, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.false_eq_true, eq_self_iff_true, ite_false, ite_true, Nat.add_zero] at hv ⊢
    constructor <;> linarith
  · intro ⟨a1, a2, a3⟩ _ ⟨c1, c2, c3⟩ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2.2 (Prod.ext h.2.1 h.1)
  · intro ⟨v1, v2, v3⟩ hv
    simp only [sClassL, exactTripleCollisionClass, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.false_eq_true, eq_self_iff_true, ite_false, ite_true, Nat.add_zero] at hv ⊢
    exact ⟨(v3, v2, v1), ⟨by linarith, by linarith⟩, rfl⟩

private theorem lftt (m : Nat) : (sClassL m false true true).card = exactWeightTriple m := by
  rw [exactWeightTriple_eq_triple_exact]; congr 1; ext ⟨v1, v2, v3⟩
  simp only [sClassL, Finset.mem_filter, Finset.mem_univ, true_and,
    Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
  constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> omega

private theorem lttt (m : Nat) : (sClassL m true true true).card = crossCorrSqLow m := by
  rw [← lfff]; congr 1; ext ⟨v1, v2, v3⟩
  simp only [sClassL, Finset.mem_filter, Finset.mem_univ, true_and, ite_true, ite_false,
    Nat.add_zero]; constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> omega

-- Empty L classes
private theorem ltff (m : Nat) : (sClassL m true false false).card = 0 := by
  simp only [sClassL, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ⟨v1, v2, v3⟩ _ ⟨h1, h2⟩
  simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at h1 h2
  have := X.weight_lt_fib v2; have : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) :=
    Nat.fib_add_two; have := Nat.fib_mono (show m + 1 ≤ m + 2 from by omega); linarith

private theorem ltft (m : Nat) : (sClassL m true false true).card = 0 := by
  simp only [sClassL, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ⟨v1, v2, v3⟩ _ ⟨h1, h2⟩
  simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at h1 h2
  have := X.weight_lt_fib v2; have : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) :=
    Nat.fib_add_two; have := Nat.fib_mono (show m + 1 ≤ m + 2 from by omega); linarith

private theorem lttf (m : Nat) : (sClassL m true true false).card = 0 := by
  simp only [sClassL, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ⟨v1, v2, v3⟩ _ ⟨h1, h2⟩
  simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at h1 h2
  have := X.weight_lt_fib v3; have : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) :=
    Nat.fib_add_two; have := Nat.fib_mono (show m + 1 ≤ m + 2 from by omega); linarith

-- ═══ Assembly ═══

/-- CCS'(m+1) = 2·EWT(m) + 4·(CCSH(m) + CCSL(m)).
    prop:pom-s3-recurrence -/
theorem ccs_prime_succ (m : Nat) :
    crossCorrSqHighPrev (m + 1) + crossCorrSqLowPrev (m + 1) =
    2 * exactWeightTriple m + 4 * (crossCorrSqHigh m + crossCorrSqLow m) := by
  rw [← shiftedTriple_eq_ccs_prime]; unfold shiftedTriple
  rw [splitH, splitL]
  simp only [Fintype.sum_prod_type, Fintype.univ_bool,
    Finset.sum_insert (by decide : true ∉ ({false} : Finset Bool)), Finset.sum_singleton]
  rw [hfff, hfft, hftf, hftt, htff, htft, httf, httt,
      lfff, lfft, lftf, lftt, ltff, ltft, lttf, lttt]
  ring

/-- EWT(m+3) + 2·EWT(m) = 2·EWT(m+2) + 4·EWT(m+1).
    prop:pom-s3-recurrence -/
theorem exactWeightTriple_recurrence (m : Nat) :
    exactWeightTriple (m + 3) + 2 * exactWeightTriple m =
    2 * exactWeightTriple (m + 2) + 4 * exactWeightTriple (m + 1) := by
  have h1 := exactWeightTriple_succ m
  have h2 : exactWeightTriple (m + 2) = 2 * exactWeightTriple (m + 1) +
      3 * crossCorrSqHigh (m + 1) + 3 * crossCorrSqLow (m + 1) := by
    have := exactWeightTriple_succ (m + 1); linarith
  have h3 : exactWeightTriple (m + 3) = 2 * exactWeightTriple (m + 2) +
      3 * crossCorrSqHigh (m + 2) + 3 * crossCorrSqLow (m + 2) := by
    have := exactWeightTriple_succ (m + 2); linarith
  have hcc1 := cc_succ_eq_ccs_prime m
  have hcc2 : crossCorrSqHigh (m + 2) + crossCorrSqLow (m + 2) =
      crossCorrSqHighPrev (m + 1) + crossCorrSqLowPrev (m + 1) := by
    have := cc_succ_eq_ccs_prime (m + 1); linarith
  have hc := ccs_prime_succ m
  linarith

/-- S_3(m+3) + 2·S_3(m) = 2·S_3(m+2) + 4·S_3(m+1) (unconditional).
    prop:pom-s3-recurrence -/
theorem momentSum_three_recurrence (m : Nat) :
    momentSum 3 (m + 3) + 2 * momentSum 3 m =
    2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1) := by
  match m with
  | 0 => simp only [← cMomentSum_eq]; native_decide
  | m + 1 =>
    show momentSum 3 (m + 4) + 2 * momentSum 3 (m + 1) =
        2 * momentSum 3 (m + 3) + 4 * momentSum 3 (m + 2)
    have d1 := momentSum_three_add_ewt m
    have d2 : momentSum 3 (m + 2) + exactWeightTriple (m + 2) =
        exactWeightTriple (m + 3) := by have := momentSum_three_add_ewt (m + 1); linarith
    have d3 : momentSum 3 (m + 3) + exactWeightTriple (m + 3) =
        exactWeightTriple (m + 4) := by have := momentSum_three_add_ewt (m + 2); linarith
    have s4 : momentSum 3 (m + 4) = exactWeightTriple (m + 4) +
        3 * crossCorrSqHighPrev (m + 3) + 3 * crossCorrSqLowPrev (m + 3) := by
      have := momentSum_three_eq_ewt_plus_ccs (m + 3); linarith
    have c3 : crossCorrSqHighPrev (m + 3) + crossCorrSqLowPrev (m + 3) =
        2 * exactWeightTriple (m + 2) +
        4 * (crossCorrSqHigh (m + 2) + crossCorrSqLow (m + 2)) := by
      have := ccs_prime_succ (m + 2); linarith
    have cc2 : crossCorrSqHigh (m + 2) + crossCorrSqLow (m + 2) =
        crossCorrSqHighPrev (m + 1) + crossCorrSqLowPrev (m + 1) := by
      have := cc_succ_eq_ccs_prime (m + 1); linarith
    have c1 := ccs_prime_succ m
    have e0 := exactWeightTriple_succ m
    have er : exactWeightTriple (m + 4) + 2 * exactWeightTriple (m + 1) =
        2 * exactWeightTriple (m + 3) + 4 * exactWeightTriple (m + 2) := by
      have := exactWeightTriple_recurrence (m + 1); linarith
    -- Goal: S(m+4) + 2S(m+1) = 2S(m+3) + 4S(m+2)
    -- From d1: S(m+1) = E(m+2) - E(m+1)
    -- From d2: S(m+2) = E(m+3) - E(m+2)
    -- From d3: S(m+3) = E(m+4) - E(m+3)
    -- From s4+c3+cc2+c1+e0: S(m+4) expressed in terms of E and B
    -- From er: E(m+4)+2E(m+1) = 2E(m+3)+4E(m+2)
    -- Using S = E_next - E and the EWT recurrence, the S_3 recurrence follows.
    -- S(m+4) = E(m+4) + 3c3' where c3' = CCS'(m+3) = 2E(m+2)+4B(m+2)
    -- S(m+1) = E(m+2) - E(m+1) [d1]
    -- S(m+2) = E(m+3) - E(m+2) [d2]
    -- S(m+3) = E(m+4) - E(m+3) [d3]
    -- er: E(m+4)+2E(m+1) = 2E(m+3)+4E(m+2)
    -- Need: S(m+4)+2S(m+1) = 2S(m+3)+4S(m+2)
    -- = S(m+4) + 2(E(m+2)-E(m+1)) = 2(E(m+4)-E(m+3)) + 4(E(m+3)-E(m+2))
    -- = S(m+4) + 2E(m+2) - 2E(m+1) = 2E(m+4) - 2E(m+3) + 4E(m+3) - 4E(m+2)
    -- = S(m+4) + 2E(m+2) - 2E(m+1) = 2E(m+4) + 2E(m+3) - 4E(m+2)
    -- Need: S(m+4) = 2E(m+4) + 2E(m+3) - 4E(m+2) - 2E(m+2) + 2E(m+1)
    --     = 2E(m+4) + 2E(m+3) - 6E(m+2) + 2E(m+1)
    -- From er: E(m+4) = 2E(m+3)+4E(m+2)-2E(m+1)
    -- → 2E(m+4) = 4E(m+3)+8E(m+2)-4E(m+1)
    -- → S(m+4) = 4E(m+3)+8E(m+2)-4E(m+1)+2E(m+3)-6E(m+2)+2E(m+1)
    --         = 6E(m+3)+2E(m+2)-2E(m+1)
    -- From s4: S(m+4) = E(m+4)+3c3'
    -- From c3: c3' = CCS'(m+3) = 2E(m+2)+4(CCSH(m+2)+CCSL(m+2))
    -- From cc2: CCSH(m+2)+CCSL(m+2) = CCSH'(m+1)+CCSL'(m+1) = CCS'(m+1)
    -- From c1: CCS'(m+1) = 2E(m)+4(CCSH(m)+CCSL(m))
    -- From e0: E(m+1) = 2E(m)+3(CCSH(m)+CCSL(m))
    -- So CCS'(m+1) = 2E(m)+4B(m) and 3B(m) = E(m+1)-2E(m) → CCS'(m+1) = (4E(m+1)-2E(m))/3
    -- → 3·CCS'(m+1) = 4E(m+1)-2E(m)
    -- c3' = 2E(m+2)+4·CCS'(m+1) = 2E(m+2)+(16E(m+1)-8E(m))/3
    -- 3c3' = 6E(m+2)+16E(m+1)-8E(m)
    -- S(m+4) = E(m+4)+6E(m+2)+16E(m+1)-8E(m))/... this is getting very messy.
    -- Let me just use enough have's to guide linarith.
    have hS4 : momentSum 3 (m + 4) + exactWeightTriple (m + 1) =
        exactWeightTriple (m + 4) + exactWeightTriple (m + 1) +
        3 * crossCorrSqHighPrev (m + 3) + 3 * crossCorrSqLowPrev (m + 3) := by linarith
    -- er gives E(m+4)+2E(m+1) = 2E(m+3)+4E(m+2)
    -- d3 gives S(m+3) = E(m+4)-E(m+3)
    -- d2 gives S(m+2) = E(m+3)-E(m+2)
    -- d1 gives S(m+1) = E(m+2)-E(m+1)
    -- From these 4: S(m+4)+2S(m+1) = S(m+4)+2E(m+2)-2E(m+1)
    -- 2S(m+3)+4S(m+2) = 2E(m+4)-2E(m+3)+4E(m+3)-4E(m+2) = 2E(m+4)+2E(m+3)-4E(m+2)
    -- Need: S(m+4)+2E(m+2)-2E(m+1) = 2E(m+4)+2E(m+3)-4E(m+2)
    -- → S(m+4) = 2E(m+4)+2E(m+3)-6E(m+2)+2E(m+1)
    -- Using er: 2E(m+4) = 4E(m+3)+8E(m+2)-4E(m+1)
    -- → S(m+4) = 6E(m+3)+2E(m+2)-2E(m+1)
    -- This requires knowing S(m+4) in terms of E values. From s4+c3+cc2+c1+e0:
    -- S(m+4) = E(m+4) + 3·(2E(m+2)+4·CCS'(m+1))
    -- = E(m+4) + 6E(m+2) + 12·CCS'(m+1)
    -- And 3·CCS'(m+1) = E(m+2)-2E(m+1)+3·CCS'(m+1)... from hcc1+e0:
    -- CCS'(m+1) (= CCSH'(m+1)+CCSL'(m+1)) related to CCSH(m+1)+CCSL(m+1) = CCS'(m)
    -- Actually hcc1 was cc_succ at m, not used here.
    -- 12·CCS'(m+1) = 12·(crossCorrSqHighPrev (m+1)+crossCorrSqLowPrev (m+1))
    -- From c1: = 12·(2E(m)+4B(m)) = 24E(m)+48B(m) = 24E(m)+16(E(m+1)-2E(m))
    -- = 16E(m+1)-8E(m)
    -- S(m+4) = E(m+4)+6E(m+2)+16E(m+1)-8E(m)
    -- Check: 6E(m+3)+2E(m+2)-2E(m+1) = E(m+4)+6E(m+2)+16E(m+1)-8E(m)?
    -- Using er: E(m+4) = 2E(m+3)+4E(m+2)-2E(m+1)
    -- RHS = 2E(m+3)+4E(m+2)-2E(m+1)+6E(m+2)+16E(m+1)-8E(m)
    --     = 2E(m+3)+10E(m+2)+14E(m+1)-8E(m)
    -- LHS = 6E(m+3)+2E(m+2)-2E(m+1)
    -- These aren't equal! Something is wrong. Let me use a different approach.
    -- Just verify both sides equal by expanding everything via linarith with enough hypotheses.
    -- The issue is that linarith can't handle the nonlinearity of 3*(...) terms.
    -- Let me try omega after expressing everything as additions.
    -- From d1: S(m+1)+E(m+1) = E(m+2)
    -- From d2: S(m+2)+E(m+2) = E(m+3)
    -- From d3: S(m+3)+E(m+3) = E(m+4)
    -- From er: E(m+4)+2E(m+1) = 2E(m+3)+4E(m+2)
    -- From s4: S(m+4) = E(m+4)+3(CCS'(m+3)) where CCS'(m+3) = 2E(m+2)+4(CCSH(m+2)+CCSL(m+2))
    -- From cc2: CCSH(m+2)+CCSL(m+2) = CCS'(m+1)
    -- From c1: CCS'(m+1) = 2E(m)+4(CCSH(m)+CCSL(m))
    -- From e0: E(m+1) = 2E(m)+3(CCSH(m)+CCSL(m))
    -- Let B := CCSH(m)+CCSL(m)
    -- e0: E(m+1) = 2E(m)+3B → 3B = E(m+1)-2E(m)
    -- c1: CCS'(m+1) = 2E(m)+4B
    -- c3: CCS'(m+3) = 2E(m+2)+4·CCS'(m+1) = 2E(m+2)+4·(2E(m)+4B) = 2E(m+2)+8E(m)+16B
    -- 3·CCS'(m+3) = 6E(m+2)+24E(m)+48B = 6E(m+2)+24E(m)+16(E(m+1)-2E(m))
    --             = 6E(m+2)+16E(m+1)-8E(m)
    -- S(m+4) = E(m+4)+6E(m+2)+16E(m+1)-8E(m) ... but this introduces division by 3.
    -- The issue: `3 * CCS'(m+3)` appears in s4 via `3 * crossCorrSqHighPrev (m+3) + 3 * crossCorrSqLowPrev (m+3)`.
    -- And `CCS'(m+3) = c3 = 2E(m+2)+4·cc2 = 2E(m+2)+4·c1 = 2E(m+2)+4·(2E(m)+4B)`.
    -- So `3·CCS'(m+3)` is computable. Let me use explicit haves.
    have h3c := c3  -- CCS'(m+3) = 2E(m+2)+4(CCSH(m+2)+CCSL(m+2))
    have hcc2' := cc2  -- CCSH(m+2)+CCSL(m+2) = CCS'(m+1)
    have hc1' := c1  -- CCS'(m+1) = 2E(m)+4B(m)
    have he0' := e0  -- E(m+1) = 2E(m)+3B(m)
    -- 3·CCS'(m+3) = 3·(2E(m+2)+4CCS'(m+1)) = 6E(m+2)+12CCS'(m+1)
    -- 12·CCS'(m+1) = 12·(2E(m)+4B) = 24E(m)+48B
    -- 48B = 16·3B = 16(E(m+1)-2E(m)) → 48B = 16E(m+1)-32E(m)
    -- 12CCS'(m+1) = 24E(m)+16E(m+1)-32E(m) = 16E(m+1)-8E(m)
    -- 3CCS'(m+3) = 6E(m+2)+16E(m+1)-8E(m)
    -- s4: S(m+4) = E(m+4) + 3CCS'(m+3)
    -- Now from d1,d2,d3:
    -- S(m+1) = E(m+2)-E(m+1)
    -- S(m+2) = E(m+3)-E(m+2)
    -- S(m+3) = E(m+4)-E(m+3)
    -- Goal: S(m+4)+2S(m+1) = 2S(m+3)+4S(m+2)
    -- LHS = E(m+4)+3CCS'(m+3)+2(E(m+2)-E(m+1))
    -- RHS = 2(E(m+4)-E(m+3))+4(E(m+3)-E(m+2))
    --     = 2E(m+4)+2E(m+3)-4E(m+2)
    -- LHS = E(m+4)+6E(m+2)+16E(m+1)-8E(m)+2E(m+2)-2E(m+1)
    --     = E(m+4)+8E(m+2)+14E(m+1)-8E(m)
    -- E(m+4) = 2E(m+3)+4E(m+2)-2E(m+1) [er]
    -- LHS = 2E(m+3)+4E(m+2)-2E(m+1)+8E(m+2)+14E(m+1)-8E(m)
    --     = 2E(m+3)+12E(m+2)+12E(m+1)-8E(m)
    -- RHS = 2E(m+4)+2E(m+3)-4E(m+2) = 2(2E(m+3)+4E(m+2)-2E(m+1))+2E(m+3)-4E(m+2)
    --     = 6E(m+3)+4E(m+2)-4E(m+1)
    -- LHS ≠ RHS unless E(m+3) and E(m+2) have specific relationships.
    -- Something is wrong with my computation. Let me recompute.
    -- From d1: S(m+1)+E(m+1) = E(m+2) → S(m+1) ≤ E(m+2)
    -- From d2: S(m+2)+E(m+2) = E(m+3) → S(m+2) ≤ E(m+3)
    -- So S+E = E'. The recurrence S(m+4)+2S(m+1) = 2S(m+3)+4S(m+2) becomes
    -- (E'-E)+2(E''-E') = 2(E'''-E'')+4(E''-E')...
    -- Let me just linarith with all hypotheses turned into equalities.
    -- d1,d2,d3 + er + s4+c3+cc2+c1+e0 should overdetermine the system.
    -- All hypotheses use addition only (no Nat subtraction issues).
    -- d1: S(m+1)+E(m+1) = E(m+2)
    -- d2: S(m+2)+E(m+2) = E(m+3)
    -- d3: S(m+3)+E(m+3) = E(m+4)
    -- er: E(m+4)+2E(m+1) = 2E(m+3)+4E(m+2)
    -- s4: S(m+4) = E(m+4)+3CCSHp3+3CCSLp3
    -- c3: CCSHp3+CCSLp3 = 2E(m+2)+4(CCSH(m+2)+CCSL(m+2))
    -- cc2: CCSH(m+2)+CCSL(m+2) = CCSHp1+CCSLp1
    -- c1: CCSHp1+CCSLp1 = 2E(m)+4B where B=CCSH(m)+CCSL(m)
    -- e0: E(m+1) = 2E(m)+3B
    -- Goal: S(m+4)+2S(m+1) = 2S(m+3)+4S(m+2)
    -- Step by step, eliminate all CC variables using only addition:
    -- From e0 and c1: 3(CCSHp1+CCSLp1) = 3(2E(m)+4B) = 6E(m)+12B = 6E(m)+4(E(m+1)-2E(m))
    -- But E(m+1)-2E(m) = 3B (from e0), so 12B = 4·3B = 4(E(m+1)-2E(m))
    -- → 6E(m)+12B = 6E(m)+4E(m+1)-8E(m) = 4E(m+1)-2E(m)
    -- So 3(CCSHp1+CCSLp1)+2E(m) = 4E(m+1) [addition form!]
    have h1 : 3 * (crossCorrSqHighPrev (m + 1) + crossCorrSqLowPrev (m + 1)) +
        2 * exactWeightTriple m = 4 * exactWeightTriple (m + 1) := by linarith
    -- From c3+cc2: CCSHp3+CCSLp3 = 2E(m+2)+4(CCSHp1+CCSLp1)
    -- So 3(CCSHp3+CCSLp3) = 6E(m+2)+12(CCSHp1+CCSLp1)
    -- = 6E(m+2)+4·3(CCSHp1+CCSLp1) = 6E(m+2)+4(4E(m+1)-2E(m)) = 6E(m+2)+16E(m+1)-8E(m)
    -- → 3(CCSHp3+CCSLp3)+8E(m) = 6E(m+2)+16E(m+1)
    have h2 : 3 * (crossCorrSqHighPrev (m + 3) + crossCorrSqLowPrev (m + 3)) +
        8 * exactWeightTriple m = 6 * exactWeightTriple (m + 2) +
        16 * exactWeightTriple (m + 1) := by linarith
    -- s4: S(m+4) = E(m+4)+3(CCSHp3+CCSLp3)
    -- → S(m+4)+8E(m) = E(m+4)+6E(m+2)+16E(m+1)
    have hS : momentSum 3 (m + 4) + 8 * exactWeightTriple m =
        exactWeightTriple (m + 4) + 6 * exactWeightTriple (m + 2) +
        16 * exactWeightTriple (m + 1) := by linarith
    -- Also need EWT recurrence at level m
    have er0 := exactWeightTriple_recurrence m
    linarith

-- ══════════════════════════════════════════════════════════════
-- Phase 163: Unconditional S_3 consequence chain
-- ══════════════════════════════════════════════════════════════

/-- S_3 is strictly monotone for m ≥ 1.
    prop:pom-s3-recurrence -/
theorem momentSum_three_strict_mono (m : Nat) (hm : 1 ≤ m) :
    momentSum 3 m < momentSum 3 (m + 1) :=
  momentSum_three_strict_mono_of momentSum_three_recurrence m

/-- S_3(m+1) ≥ 2·S_3(m) for m ≥ 2.
    prop:pom-s3-recurrence -/
theorem momentSum_three_double (m : Nat) (hm : 2 ≤ m) :
    2 * momentSum 3 m ≤ momentSum 3 (m + 1) :=
  momentSum_three_double_of momentSum_three_recurrence m hm

/-- S_3(m) is even for m ≥ 1.
    prop:pom-s3-recurrence -/
theorem momentSum_three_even (m : Nat) (hm : 1 ≤ m) :
    2 ∣ momentSum 3 m :=
  momentSum_three_even_of momentSum_three_recurrence m hm

/-- S_3(8) = 7768.
    prop:pom-s3-recurrence -/
theorem momentSum_three_eight : momentSum 3 8 = 7768 :=
  momentSum_three_eight_of momentSum_three_recurrence

/-- S_3(9) = 23912.
    prop:pom-s3-recurrence -/
theorem momentSum_three_nine : momentSum 3 9 = 23912 :=
  momentSum_three_nine_of momentSum_three_recurrence

/-- S_3(10) = 73888.
    prop:pom-s3-recurrence -/
theorem momentSum_three_ten : momentSum 3 10 = 73888 :=
  momentSum_three_ten_of momentSum_three_recurrence

/-- S_3 subtraction form.
    prop:pom-s3-recurrence -/
theorem momentSum_three_recurrence_sub (m : Nat) :
    momentSum 3 (m + 3) = 2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1) -
      2 * momentSum 3 m :=
  momentSum_three_recurrence_sub_of momentSum_three_recurrence m

-- ══════════════════════════════════════════════════════════════
-- Phase 164: S_3 lower bound + high-order base values
-- ══════════════════════════════════════════════════════════════

/-- 2^m · S_3(m) ≥ S_2(m)² (log-convexity consequence).
    prop:pom-moment-congruence-q -/
theorem momentSum_three_ge_sq_div (m : Nat) :
    2 ^ m * momentSum 3 m ≥ momentSum 2 m ^ 2 := by
  have := momentSum_log_convex 1 m
  rw [momentSum_one] at this
  linarith

/-- S_3(11) = 227888.
    prop:pom-s3-recurrence -/
theorem momentSum_three_eleven : momentSum 3 11 = 227888 := by
  have h : momentSum 3 11 + 2 * 7768 = 2 * 73888 + 4 * 23912 := by
    have := momentSum_three_recurrence 8
    change momentSum 3 11 + 2 * momentSum 3 8 = 2 * momentSum 3 10 + 4 * momentSum 3 9 at this
    rw [momentSum_three_eight, momentSum_three_nine, momentSum_three_ten] at this; linarith
  omega

/-- S_3(12) = 703504.
    prop:pom-s3-recurrence -/
theorem momentSum_three_twelve : momentSum 3 12 = 703504 := by
  have h : momentSum 3 12 + 2 * 23912 = 2 * 227888 + 4 * 73888 := by
    have := momentSum_three_recurrence 9
    change momentSum 3 12 + 2 * momentSum 3 9 = 2 * momentSum 3 11 + 4 * momentSum 3 10 at this
    rw [momentSum_three_nine, momentSum_three_ten, momentSum_three_eleven] at this; linarith
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase 165: EWT strict monotonicity + CCS recurrence
-- ══════════════════════════════════════════════════════════════

private theorem exactWeightTriple_pos (m : Nat) : 0 < exactWeightTriple m := by
  unfold exactWeightTriple
  have h0 : 0 ∈ Finset.range (Nat.fib (m + 3)) :=
    Finset.mem_range.mpr (Nat.fib_pos.mpr (by omega))
  have h1 : exactWeightCount m 0 ^ 3 = 1 := by rw [exactWeightCount_zero_eq_one']; norm_num
  linarith [Finset.single_le_sum (fun _ _ => Nat.zero_le _) h0
    (f := fun n => exactWeightCount m n ^ 3)]

/-- EWT is strictly monotone for m ≥ 1.
    bridge:ewt-strict-mono -/
theorem exactWeightTriple_strict_mono (m : Nat) (hm : 1 ≤ m) :
    exactWeightTriple m < exactWeightTriple (m + 1) := by
  have h := exactWeightTriple_succ m
  have hpos := exactWeightTriple_pos m
  linarith

/-- CCS(m+3) + 2·CCS(m) = 2·CCS(m+2) + 4·CCS(m+1), where CCS = CCSH+CCSL.
    bridge:ccs-f-recurrence -/
theorem crossCorrSq_recurrence (m : Nat) :
    (crossCorrSqHigh (m + 3) + crossCorrSqLow (m + 3)) +
    2 * (crossCorrSqHigh m + crossCorrSqLow m) =
    2 * (crossCorrSqHigh (m + 2) + crossCorrSqLow (m + 2)) +
    4 * (crossCorrSqHigh (m + 1) + crossCorrSqLow (m + 1)) := by
  have hcc2 : crossCorrSqHigh (m + 2) + crossCorrSqLow (m + 2) =
      crossCorrSqHighPrev (m + 1) + crossCorrSqLowPrev (m + 1) := by
    have := cc_succ_eq_ccs_prime (m + 1); linarith
  have hcc3 : crossCorrSqHigh (m + 3) + crossCorrSqLow (m + 3) =
      crossCorrSqHighPrev (m + 2) + crossCorrSqLowPrev (m + 2) := by
    have := cc_succ_eq_ccs_prime (m + 2); linarith
  have hcp1 := ccs_prime_succ m
  have hcp2 : crossCorrSqHighPrev (m + 2) + crossCorrSqLowPrev (m + 2) =
      2 * exactWeightTriple (m + 1) +
      4 * (crossCorrSqHigh (m + 1) + crossCorrSqLow (m + 1)) := by
    have := ccs_prime_succ (m + 1); linarith
  have he := exactWeightTriple_succ m
  linarith

/-- CCS' satisfies the same three-step recurrence as S_3 and EWT.
    bridge:ccs-prime-recurrence -/
theorem ccs_prime_recurrence (m : Nat) :
    crossCorrSqHighPrev (m + 3) + crossCorrSqLowPrev (m + 3) +
    2 * (crossCorrSqHighPrev m + crossCorrSqLowPrev m) =
    2 * (crossCorrSqHighPrev (m + 2) + crossCorrSqLowPrev (m + 2)) +
    4 * (crossCorrSqHighPrev (m + 1) + crossCorrSqLowPrev (m + 1)) := by
  have h0 := ccs_prime_succ m
  have h1 : crossCorrSqHighPrev (m + 2) + crossCorrSqLowPrev (m + 2) =
      2 * exactWeightTriple (m + 1) +
      4 * (crossCorrSqHigh (m + 1) + crossCorrSqLow (m + 1)) := by
    have := ccs_prime_succ (m + 1); linarith
  have h2 : crossCorrSqHighPrev (m + 3) + crossCorrSqLowPrev (m + 3) =
      2 * exactWeightTriple (m + 2) +
      4 * (crossCorrSqHigh (m + 2) + crossCorrSqLow (m + 2)) := by
    have := ccs_prime_succ (m + 2); linarith
  -- CCS'(k) = CCS(k+1) by cc_succ. So the goal is CCS(m+4)+2CCS(m+1)=2CCS(m+3)+4CCS(m+2),
  -- which is crossCorrSq_recurrence at m+1.
  have hcc0 := cc_succ_eq_ccs_prime m
  have hcc1 : crossCorrSqHigh (m + 2) + crossCorrSqLow (m + 2) =
      crossCorrSqHighPrev (m + 1) + crossCorrSqLowPrev (m + 1) := by
    have := cc_succ_eq_ccs_prime (m + 1); linarith
  have hcc2 : crossCorrSqHigh (m + 3) + crossCorrSqLow (m + 3) =
      crossCorrSqHighPrev (m + 2) + crossCorrSqLowPrev (m + 2) := by
    have := cc_succ_eq_ccs_prime (m + 2); linarith
  have hcc3 : crossCorrSqHigh (m + 4) + crossCorrSqLow (m + 4) =
      crossCorrSqHighPrev (m + 3) + crossCorrSqLowPrev (m + 3) := by
    have := cc_succ_eq_ccs_prime (m + 3); linarith
  have ccs_rec : (crossCorrSqHigh (m + 4) + crossCorrSqLow (m + 4)) +
      2 * (crossCorrSqHigh (m + 1) + crossCorrSqLow (m + 1)) =
      2 * (crossCorrSqHigh (m + 3) + crossCorrSqLow (m + 3)) +
      4 * (crossCorrSqHigh (m + 2) + crossCorrSqLow (m + 2)) := by
    have := crossCorrSq_recurrence (m + 1); linarith
  linarith

-- ══════════════════════════════════════════════════════════════
-- Phase R33: S_3 recurrence uniqueness
-- ══════════════════════════════════════════════════════════════

/-- A 3rd-order recurrence with S_3 coefficients is uniquely determined by initial values.
    thm:pom-s3-recurrence-unique -/
private theorem recurrence_unique_s3 {f g : Nat → Nat}
    (hf : ∀ m, f (m + 3) + 2 * f m = 2 * f (m + 2) + 4 * f (m + 1))
    (hg : ∀ m, g (m + 3) + 2 * g m = 2 * g (m + 2) + 4 * g (m + 1))
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2 : f 2 = g 2) :
    ∀ m, f m = g m := by
  intro m; induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => exact h0
    | 1 => exact h1
    | 2 => exact h2
    | m + 3 =>
      have := hf m; have := hg m
      have := ih m (by omega); have := ih (m + 1) (by omega); have := ih (m + 2) (by omega)
      omega

/-- S_3 is the unique sequence satisfying f(m+3)+2f(m) = 2f(m+2)+4f(m+1) with
    initial values f(0)=1, f(1)=2, f(2)=10.
    thm:mul-from-successor -/
theorem momentSum_three_determined {f : Nat → Nat}
    (hrec : ∀ m, f (m + 3) + 2 * f m = 2 * f (m + 2) + 4 * f (m + 1))
    (h0 : f 0 = 1) (h1 : f 1 = 2) (h2 : f 2 = 10) :
    ∀ m, f m = momentSum 3 m :=
  recurrence_unique_s3 hrec momentSum_three_recurrence
    (by rw [h0, momentSum_three_zero])
    (by rw [h1, momentSum_three_one])
    (by rw [h2, momentSum_three_two])

-- ══════════════════════════════════════════════════════════════
-- Phase R34: S_3 high-order values by pure recurrence
-- ══════════════════════════════════════════════════════════════

/-- S_3(13) = 2170784.
    prop:pom-s3-recurrence -/
theorem momentSum_three_thirteen : momentSum 3 13 = 2170784 := by
  have h : momentSum 3 13 + 2 * 73888 = 2 * 703504 + 4 * 227888 := by
    have := momentSum_three_recurrence 10
    change momentSum 3 13 + 2 * momentSum 3 10 = 2 * momentSum 3 12 + 4 * momentSum 3 11 at this
    rw [momentSum_three_ten, momentSum_three_eleven, momentSum_three_twelve] at this; linarith
  omega

/-- S_3(14) = 6699808.
    prop:pom-s3-fourteen -/
theorem momentSum_three_fourteen : momentSum 3 14 = 6699808 := by
  have h : momentSum 3 14 + 2 * 227888 = 2 * 2170784 + 4 * 703504 := by
    have := momentSum_three_recurrence 11
    change momentSum 3 14 + 2 * momentSum 3 11 = 2 * momentSum 3 13 + 4 * momentSum 3 12 at this
    rw [momentSum_three_eleven, momentSum_three_twelve, momentSum_three_thirteen] at this; linarith
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase R70: S_3 superadditivity + S_3(15)
-- ══════════════════════════════════════════════════════════════

/-- S_3(m+1) + S_3(m) ≤ S_3(m+2) for m ≥ 1 (Fibonacci-type superadditivity).
    From recurrence at (m-1): S_3(m+2) = 2S_3(m+1) + 4S_3(m) - 2S_3(m-1).
    So S_3(m+2) - S_3(m+1) - S_3(m) = S_3(m+1) + 3S_3(m) - 2S_3(m-1) ≥ 0.
    thm:pom-s3-fib-superadditive -/
theorem momentSum_three_fib_superadditive (m : Nat) (hm : 1 ≤ m) :
    momentSum 3 (m + 1) + momentSum 3 m ≤ momentSum 3 (m + 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  -- Recurrence at k: S3(k+3) + 2*S3(k) = 2*S3(k+2) + 4*S3(k+1)
  have hrec := momentSum_three_recurrence k
  -- Goal: S3(k+2) + S3(k+1) ≤ S3(k+3)
  -- From hrec: S3(k+3) = 2*S3(k+2) + 4*S3(k+1) - 2*S3(k)
  -- Need: S3(k+2) + 3*S3(k+1) ≥ 2*S3(k)
  -- From S3(k+1) ≥ S3(k) (monotonicity): 3*S3(k+1) ≥ 3*S3(k) ≥ 2*S3(k)
  have hmono : momentSum 3 k ≤ momentSum 3 (k + 1) := by
    rcases k with _ | k
    · simp [← cMomentSum_eq]
    · exact Nat.le_of_lt (momentSum_three_strict_mono (k + 1) (by omega))
  linarith

/-- S_3(15) = 20675744.
    prop:pom-s3-fifteen -/
theorem momentSum_three_fifteen : momentSum 3 15 = 20675744 := by
  have h := momentSum_three_recurrence 12
  rw [show (12 : Nat) + 1 = 13 from rfl, show (12 : Nat) + 2 = 14 from rfl,
    show (12 : Nat) + 3 = 15 from rfl,
    momentSum_three_twelve, momentSum_three_thirteen, momentSum_three_fourteen] at h
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase R72: S_3(16) chain value
-- ══════════════════════════════════════════════════════════════

/-- S_3(16) = 63809152.
    prop:pom-s3-sixteen -/
theorem momentSum_three_sixteen : momentSum 3 16 = 63809152 := by
  have h := momentSum_three_recurrence 13
  rw [show (13 : Nat) + 1 = 14 from rfl, show (13 : Nat) + 2 = 15 from rfl,
    show (13 : Nat) + 3 = 16 from rfl,
    momentSum_three_thirteen, momentSum_three_fourteen, momentSum_three_fifteen] at h
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase R156: S_3(17) and S_3(18) chain values
-- ══════════════════════════════════════════════════════════════

/-- S_3(17) = 196921664.
    prop:pom-s3-seventeen -/
theorem momentSum_three_seventeen : momentSum 3 17 = 196921664 := by
  have h := momentSum_three_recurrence 14
  rw [show (14 : Nat) + 1 = 15 from rfl, show (14 : Nat) + 2 = 16 from rfl,
    show (14 : Nat) + 3 = 17 from rfl,
    momentSum_three_fourteen, momentSum_three_fifteen, momentSum_three_sixteen] at h
  omega

/-- S_3(18) = 607728448.
    prop:pom-s3-eighteen -/
theorem momentSum_three_eighteen : momentSum 3 18 = 607728448 := by
  have h := momentSum_three_recurrence 15
  rw [show (15 : Nat) + 1 = 16 from rfl, show (15 : Nat) + 2 = 17 from rfl,
    show (15 : Nat) + 3 = 18 from rfl,
    momentSum_three_fifteen, momentSum_three_sixteen, momentSum_three_seventeen] at h
  omega

end Omega
