import Omega.Folding.FiberWeightCount
import Omega.Folding.CollisionZeta
import Mathlib.Algebra.Order.Chebyshev

namespace Omega

-- ══════════════════════════════════════════════════════════════
-- wcc sum = 2^m (partition identity)
-- ══════════════════════════════════════════════════════════════

/-- Weight congruence classes partition Word m: Σ_r wcc(m,r) = 2^m. -/
theorem weightCongruenceCount_sum (m : Nat) :
    ∑ r ∈ Finset.range (Nat.fib (m + 2)), weightCongruenceCount m r = 2 ^ m := by
  -- Σ_{x:X m} d(x) = 2^m
  have h := X.fiberMultiplicity_sum_eq_pow m
  -- d(x) = wcc(sv(x))
  simp_rw [fiberMultiplicity_eq_wcc] at h
  -- Reparametrize via stableValueFin bijection
  have hbij := X.stableValueFin_bijective m
  have step : ∑ x : X m, weightCongruenceCount m (stableValue x) =
      ∑ r : Fin (Nat.fib (m + 2)), weightCongruenceCount m r.val := by
    rw [show (fun x : X m => weightCongruenceCount m (stableValue x)) =
      (fun r : Fin (Nat.fib (m + 2)) => weightCongruenceCount m r.val) ∘
      X.stableValueFin from by ext x; simp [X.stableValueFin]]
    exact hbij.sum_comp (fun r : Fin (Nat.fib (m + 2)) => weightCongruenceCount m r.val)
  rw [step] at h; rw [← Fin.sum_univ_eq_sum_range]; exact h

-- ══════════════════════════════════════════════════════════════
-- S_2 last-bit split into 4 collision classes
-- ══════════════════════════════════════════════════════════════

/-- S_2(m+1) splits into 4 collision classes by last bits. -/
theorem momentSum_two_lastBit_split (m : Nat) :
    momentSum 2 (m + 1) =
    (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 % Nat.fib (m + 3) = weight p.2 % Nat.fib (m + 3))).card +
    (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 % Nat.fib (m + 3) =
      (weight p.2 + Nat.fib (m + 2)) % Nat.fib (m + 3))).card +
    (Finset.univ.filter (fun p : Word m × Word m =>
      (weight p.1 + Nat.fib (m + 2)) % Nat.fib (m + 3) =
      weight p.2 % Nat.fib (m + 3))).card +
    (Finset.univ.filter (fun p : Word m × Word m =>
      (weight p.1 + Nat.fib (m + 2)) % Nat.fib (m + 3) =
      (weight p.2 + Nat.fib (m + 2)) % Nat.fib (m + 3))).card := by
  classical
  rw [momentSum_two_eq_collision]
  simp_rw [Fold_eq_iff_weight_mod]
  rw [show Nat.fib ((m + 1) + 2) = Nat.fib (m + 3) from by ring_nf]
  -- For each b1 b2 : Bool, the subset with last bits (b1,b2) bijects to the target via truncate
  have key : ∀ b1 b2 : Bool,
      (Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) =>
        weight p.1 % Nat.fib (m + 3) = weight p.2 % Nat.fib (m + 3) ∧
        p.1 ⟨m, by omega⟩ = b1 ∧ p.2 ⟨m, by omega⟩ = b2)).card =
      (Finset.univ.filter (fun p : Word m × Word m =>
        (weight p.1 + if b1 then Nat.fib (m + 2) else 0) % Nat.fib (m + 3) =
        (weight p.2 + if b2 then Nat.fib (m + 2) else 0) % Nat.fib (m + 3))).card := by
    intro b1 b2
    apply Finset.card_bij (fun (p : Word (m + 1) × Word (m + 1)) _ =>
      (truncate p.1, truncate p.2))
    · intro ⟨w1, w2⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rw [weight, hp.2.1, weight, hp.2.2] at hp; exact hp.1
    · intro ⟨w1a, w2a⟩ ha ⟨w1b, w2b⟩ hb heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at ha hb heq ⊢
      exact ⟨by rw [← X.snoc_truncate_last w1a, ← X.snoc_truncate_last w1b,
                     heq.1, ha.2.1, hb.2.1],
             by rw [← X.snoc_truncate_last w2a, ← X.snoc_truncate_last w2b,
                     heq.2, ha.2.2, hb.2.2]⟩
    · intro ⟨v1, v2⟩ hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ⟨(snoc v1 b1, snoc v2 b2),
        ⟨by simp [weight_snoc]; exact hv, by simp, by simp⟩, by simp⟩
  -- Partition and rewrite
  have hdisj : ∀ b1 b2 b1' b2' : Bool, (b1, b2) ≠ (b1', b2') →
      Disjoint
        (Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) =>
          weight p.1 % Nat.fib (m + 3) = weight p.2 % Nat.fib (m + 3) ∧
          p.1 ⟨m, by omega⟩ = b1 ∧ p.2 ⟨m, by omega⟩ = b2))
        (Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) =>
          weight p.1 % Nat.fib (m + 3) = weight p.2 % Nat.fib (m + 3) ∧
          p.1 ⟨m, by omega⟩ = b1' ∧ p.2 ⟨m, by omega⟩ = b2')) := by
    intro b1 b2 b1' b2' hne
    apply Finset.disjoint_filter.mpr
    intro ⟨w1, w2⟩ _ ⟨_, hb1, hb2⟩ ⟨_, hb1', hb2'⟩
    exact hne (Prod.ext (hb1.symm.trans hb1') (hb2.symm.trans hb2'))
  have hunion : Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) =>
      weight p.1 % Nat.fib (m + 3) = weight p.2 % Nat.fib (m + 3)) =
      Finset.univ.filter (fun p => weight p.1 % Nat.fib (m + 3) = weight p.2 % Nat.fib (m + 3) ∧
        p.1 ⟨m, by omega⟩ = false ∧ p.2 ⟨m, by omega⟩ = false) ∪
      Finset.univ.filter (fun p => weight p.1 % Nat.fib (m + 3) = weight p.2 % Nat.fib (m + 3) ∧
        p.1 ⟨m, by omega⟩ = false ∧ p.2 ⟨m, by omega⟩ = true) ∪
      Finset.univ.filter (fun p => weight p.1 % Nat.fib (m + 3) = weight p.2 % Nat.fib (m + 3) ∧
        p.1 ⟨m, by omega⟩ = true ∧ p.2 ⟨m, by omega⟩ = false) ∪
      Finset.univ.filter (fun p => weight p.1 % Nat.fib (m + 3) = weight p.2 % Nat.fib (m + 3) ∧
        p.1 ⟨m, by omega⟩ = true ∧ p.2 ⟨m, by omega⟩ = true) := by
    ext ⟨w1, w2⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h
      rcases Bool.eq_false_or_eq_true (w1 ⟨m, by omega⟩) with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (w2 ⟨m, by omega⟩) with h2 | h2 <;>
        simp [h, h1, h2]
    · rintro (((⟨h, _, _⟩ | ⟨h, _, _⟩) | ⟨h, _, _⟩) | ⟨h, _, _⟩) <;> exact h
  rw [hunion]
  -- Compute card of the 4-union using disjointness
  have dAB := hdisj false false false true (by decide)
  have dAC := hdisj false false true false (by decide)
  have dAD := hdisj false false true true (by decide)
  have dBC := hdisj false true true false (by decide)
  have dBD := hdisj false true true true (by decide)
  have dCD := hdisj true false true true (by decide)
  simp only [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_left.mpr ⟨dAD, dBD⟩, dCD⟩),
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨dAC, dBC⟩),
    Finset.card_union_of_disjoint dAB]
  rw [key false false, key false true, key true false, key true true]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

-- ══════════════════════════════════════════════════════════════
-- E(1,1) = E(0,0): matching last bits cancel
-- ══════════════════════════════════════════════════════════════

/-- When both last bits match, the F_{m+2} terms cancel mod F_{m+3}. -/
theorem collision_lastBit_cancel (m : Nat) :
    (Finset.univ.filter (fun p : Word m × Word m =>
      (weight p.1 + Nat.fib (m + 2)) % Nat.fib (m + 3) =
      (weight p.2 + Nat.fib (m + 2)) % Nat.fib (m + 3))).card =
    (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 % Nat.fib (m + 3) = weight p.2 % Nat.fib (m + 3))).card := by
  congr 1; ext ⟨v1, v2⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- (a + c) % n = (b + c) % n ↔ a % n = b % n
  -- Use Nat.ModEq machinery
  show Nat.ModEq (Nat.fib (m + 3)) (weight v1 + Nat.fib (m + 2)) (weight v2 + Nat.fib (m + 2)) ↔
       Nat.ModEq (Nat.fib (m + 3)) (weight v1) (weight v2)
  exact ⟨Nat.ModEq.add_right_cancel' _, fun h => h.add_right _⟩

-- ══════════════════════════════════════════════════════════════
-- E(0,1) = E(1,0) by swap symmetry
-- ══════════════════════════════════════════════════════════════

/-- Cross-collision terms are symmetric: E(0,1) = E(1,0). -/
theorem collision_cross_symm (m : Nat) :
    (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 % Nat.fib (m + 3) =
      (weight p.2 + Nat.fib (m + 2)) % Nat.fib (m + 3))).card =
    (Finset.univ.filter (fun p : Word m × Word m =>
      (weight p.1 + Nat.fib (m + 2)) % Nat.fib (m + 3) =
      weight p.2 % Nat.fib (m + 3))).card := by
  apply Finset.card_bij (fun (p : Word m × Word m) _ => (p.2, p.1))
  · intro ⟨v1, v2⟩ hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv.symm
  · intro ⟨a1, a2⟩ _ ⟨b1, b2⟩ _ h
    simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
  · intro ⟨v1, v2⟩ hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨(v2, v1), hv.symm, rfl⟩

-- ══════════════════════════════════════════════════════════════
-- S_2(m+1) = 2·E(0,0) + 2·E(0,1)
-- ══════════════════════════════════════════════════════════════

/-- S_2(m+1) decomposes into two doubled terms. -/
theorem momentSum_two_succ_two_term (m : Nat) :
    momentSum 2 (m + 1) =
    2 * (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 % Nat.fib (m + 3) = weight p.2 % Nat.fib (m + 3))).card +
    2 * (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 % Nat.fib (m + 3) =
      (weight p.2 + Nat.fib (m + 2)) % Nat.fib (m + 3))).card := by
  rw [momentSum_two_lastBit_split, collision_lastBit_cancel, collision_cross_symm]; ring

-- ══════════════════════════════════════════════════════════════
-- E(0,0) = Σ ewc(m,n)² (exact weight collision)
-- ══════════════════════════════════════════════════════════════

/-- Sum of squared exact weight counts. -/
def exactWeightCollision (m : Nat) : Nat :=
  ∑ n ∈ Finset.range (Nat.fib (m + 3)), exactWeightCount m n ^ 2

/-- E(0,0) equals the sum of squared exact weight counts. -/
theorem collision_same_eq_exactWeightCollision (m : Nat) :
    (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 % Nat.fib (m + 3) = weight p.2 % Nat.fib (m + 3))).card =
    exactWeightCollision m := by
  classical
  -- Since weight < F_{m+3}, mod is identity: condition simplifies to weight v1 = weight v2
  have hmod_id : ∀ v : Word m, weight v % Nat.fib (m + 3) = weight v := by
    intro v; exact Nat.mod_eq_of_lt (X.weight_lt_fib v)
  simp_rw [hmod_id]
  -- Now: |{(v1,v2) : weight v1 = weight v2}| = Σ_n ewc(m,n)²
  -- Partition by the common weight value
  unfold exactWeightCollision exactWeightCount
  -- |{(v1,v2) : weight v1 = weight v2}| = Σ_n |{v1 : weight v1 = n}|²
  -- = Σ_n |{v1 : weight v1 = n}| · |{v2 : weight v2 = n}|
  -- = Σ_n |{(v1,v2) : weight v1 = n ∧ weight v2 = n}|
  -- = |⊔_n {(v1,v2) : weight v1 = n ∧ weight v2 = n}|  (disjoint union)
  -- = |{(v1,v2) : weight v1 = weight v2}|
  -- Convert ewc(n)² = |{v1: wt=n} ×ˢ {v2: wt=n}|
  have hprod : ∀ n, (Finset.univ.filter (fun w : Word m => weight w = n)).card ^ 2 =
      ((Finset.univ.filter (fun w : Word m => weight w = n)) ×ˢ
       (Finset.univ.filter (fun w : Word m => weight w = n))).card := by
    intro n; rw [sq, ← Finset.card_product]
  simp_rw [hprod]
  -- Now: Σ_n |Sn ×ˢ Sn| = |⊔_n (Sn ×ˢ Sn)| = |{(v1,v2) : wt v1 = wt v2}|
  symm
  rw [← Finset.card_biUnion]
  · congr 1; ext ⟨v1, v2⟩
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨n, _, h1, h2⟩; rw [h1, h2]
    · intro h; exact ⟨weight v1, X.weight_lt_fib v1, rfl, h.symm⟩
  · intro n _ n' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro ⟨v1, _⟩ ⟨h1, _⟩ ⟨h2, _⟩
    exact hne (h1.symm.trans h2)

-- ══════════════════════════════════════════════════════════════
-- Cross-weight correlation
-- ══════════════════════════════════════════════════════════════

/-- Cross-weight correlation: Σ_r ewc(m,r) · ewc(m,r+F).
    def:pom-crossWeightCorrelation -/
def crossWeightCorrelation (m : Nat) : Nat :=
  ∑ r ∈ Finset.range (Nat.fib (m + 2)),
    exactWeightCount m r * exactWeightCount m (r + Nat.fib (m + 2))


-- ══════════════════════════════════════════════════════════════
-- E(0,0)(m+1) = E(0,0)(m) + S_2(m)
-- ══════════════════════════════════════════════════════════════

/-- thm:pom-e00-succ -/
theorem exactWeightCollision_succ (m : Nat) :
    exactWeightCollision (m + 1) = exactWeightCollision m + momentSum 2 m := by
  classical
  rw [← collision_same_eq_exactWeightCollision (m + 1),
      ← collision_same_eq_exactWeightCollision m, momentSum_two_eq_collision]
  have hmod_id1 : ∀ w : Word (m + 1), weight w % Nat.fib (m + 4) = weight w := by
    intro w; exact Nat.mod_eq_of_lt (X.weight_lt_fib w)
  have hmod_id0 : ∀ w : Word m, weight w % Nat.fib (m + 3) = weight w := by
    intro w; exact Nat.mod_eq_of_lt (X.weight_lt_fib w)
  simp_rw [hmod_id1, hmod_id0, Fold_eq_iff_weight_mod]
  have key : ∀ b1 b2 : Bool,
      (Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) =>
        weight p.1 = weight p.2 ∧ p.1 ⟨m, by omega⟩ = b1 ∧ p.2 ⟨m, by omega⟩ = b2)).card =
      (Finset.univ.filter (fun p : Word m × Word m =>
        weight p.1 + (if b1 then Nat.fib (m + 2) else 0) =
        weight p.2 + (if b2 then Nat.fib (m + 2) else 0))).card := by
    intro b1 b2
    apply Finset.card_bij (fun (p : Word (m + 1) × Word (m + 1)) _ => (truncate p.1, truncate p.2))
    · intro ⟨w1, w2⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rw [weight, hp.2.1, weight, hp.2.2] at hp; exact hp.1
    · intro ⟨w1a, w2a⟩ ha ⟨w1b, w2b⟩ hb heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at ha hb heq ⊢
      exact ⟨by rw [← X.snoc_truncate_last w1a, ← X.snoc_truncate_last w1b, heq.1, ha.2.1, hb.2.1],
             by rw [← X.snoc_truncate_last w2a, ← X.snoc_truncate_last w2b, heq.2, ha.2.2, hb.2.2]⟩
    · intro ⟨v1, v2⟩ hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ⟨(snoc v1 b1, snoc v2 b2), ⟨by simp [weight_snoc]; exact hv, by simp, by simp⟩, by simp⟩
  have hdisj : ∀ b1 b2 b1' b2' : Bool, (b1, b2) ≠ (b1', b2') → Disjoint
      (Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) =>
        weight p.1 = weight p.2 ∧ p.1 ⟨m, by omega⟩ = b1 ∧ p.2 ⟨m, by omega⟩ = b2))
      (Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) =>
        weight p.1 = weight p.2 ∧ p.1 ⟨m, by omega⟩ = b1' ∧ p.2 ⟨m, by omega⟩ = b2')) := by
    intro b1 b2 b1' b2' hne; apply Finset.disjoint_filter.mpr
    intro ⟨w1, w2⟩ _ ⟨_, hb1, hb2⟩ ⟨_, hb1', hb2'⟩
    exact hne (Prod.ext (hb1.symm.trans hb1') (hb2.symm.trans hb2'))
  have hunion : Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) => weight p.1 = weight p.2) =
      Finset.univ.filter (fun p => weight p.1 = weight p.2 ∧ p.1 ⟨m, by omega⟩ = false ∧ p.2 ⟨m, by omega⟩ = false) ∪
      Finset.univ.filter (fun p => weight p.1 = weight p.2 ∧ p.1 ⟨m, by omega⟩ = false ∧ p.2 ⟨m, by omega⟩ = true) ∪
      Finset.univ.filter (fun p => weight p.1 = weight p.2 ∧ p.1 ⟨m, by omega⟩ = true ∧ p.2 ⟨m, by omega⟩ = false) ∪
      Finset.univ.filter (fun p => weight p.1 = weight p.2 ∧ p.1 ⟨m, by omega⟩ = true ∧ p.2 ⟨m, by omega⟩ = true) := by
    ext ⟨w1, w2⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h; rcases Bool.eq_false_or_eq_true (w1 ⟨m, by omega⟩) with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (w2 ⟨m, by omega⟩) with h2 | h2 <;> simp [h, h1, h2]
    · rintro (((⟨h, _, _⟩ | ⟨h, _, _⟩) | ⟨h, _, _⟩) | ⟨h, _, _⟩) <;> exact h
  rw [hunion]
  have dAB := hdisj false false false true (by decide)
  have dAC := hdisj false false true false (by decide)
  have dAD := hdisj false false true true (by decide)
  have dBC := hdisj false true true false (by decide)
  have dBD := hdisj false true true true (by decide)
  have dCD := hdisj true false true true (by decide)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨dAD, dBD⟩, dCD⟩),
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨dAC, dBC⟩),
    Finset.card_union_of_disjoint dAB,
    key false false, key false true, key true false, key true true]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  have htt : (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 + Nat.fib (m + 2) = weight p.2 + Nat.fib (m + 2))).card =
      (Finset.univ.filter (fun p : Word m × Word m => weight p.1 = weight p.2)).card := by
    congr 1; ext ⟨v1, v2⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  rw [htt]
  have hmod_split : (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 % Nat.fib (m + 2) = weight p.2 % Nat.fib (m + 2))).card =
      (Finset.univ.filter (fun p : Word m × Word m => weight p.1 = weight p.2)).card +
      (Finset.univ.filter (fun p : Word m × Word m => weight p.1 = weight p.2 + Nat.fib (m + 2))).card +
      (Finset.univ.filter (fun p : Word m × Word m => weight p.1 + Nat.fib (m + 2) = weight p.2)).card := by
    have hlt2F : ∀ v : Word m, weight v < 2 * Nat.fib (m + 2) := by
      intro v
      have hf3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
      have hmono : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
      have hwt := X.weight_lt_fib v
      omega
    have hsplit : Finset.univ.filter (fun p : Word m × Word m =>
        weight p.1 % Nat.fib (m + 2) = weight p.2 % Nat.fib (m + 2)) =
        Finset.univ.filter (fun p : Word m × Word m => weight p.1 = weight p.2) ∪
        Finset.univ.filter (fun p => weight p.1 = weight p.2 + Nat.fib (m + 2)) ∪
        Finset.univ.filter (fun p => weight p.1 + Nat.fib (m + 2) = weight p.2) := by
      ext ⟨v1, v2⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro hmod
        have hdiv1 := Nat.div_add_mod (weight v1) (Nat.fib (m + 2))
        have hdiv2 := Nat.div_add_mod (weight v2) (Nat.fib (m + 2))
        have hq1 : weight v1 / Nat.fib (m + 2) < 2 :=
          Nat.div_lt_of_lt_mul (show weight v1 < Nat.fib (m + 2) * 2 by linarith [hlt2F v1])
        have hq2 : weight v2 / Nat.fib (m + 2) < 2 :=
          Nat.div_lt_of_lt_mul (show weight v2 < Nat.fib (m + 2) * 2 by linarith [hlt2F v2])
        rw [hmod] at hdiv1
        interval_cases (weight v1 / Nat.fib (m + 2)) <;>
          interval_cases (weight v2 / Nat.fib (m + 2)) <;> simp_all <;> omega
      · rintro ((h | h) | h)
        · rw [h]
        · rw [h, Nat.add_mod_right]
        · have : weight v2 = weight v1 + Nat.fib (m + 2) := by omega
          rw [this, Nat.add_mod_right]
    have hFpos : 0 < Nat.fib (m + 2) := fib_succ_pos (m + 1)
    rw [hsplit,
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_filter.mpr (fun ⟨_, _⟩ _ h1 h2 => by omega),
         Finset.disjoint_filter.mpr (fun ⟨_, _⟩ _ h1 h2 => by omega)⟩),
      Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr (fun ⟨_, _⟩ _ h1 h2 => by omega))]
  rw [hmod_split]; omega

-- ══════════════════════════════════════════════════════════════
-- E(0,0) telescoping sum
-- ══════════════════════════════════════════════════════════════

/-- thm:pom-e00-telescoping -/
theorem exactWeightCollision_eq_sum (m : Nat) :
    exactWeightCollision m = 1 + ∑ k ∈ Finset.range m, momentSum 2 k := by
  induction m with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.add_zero]
    unfold exactWeightCollision
    simp only [show Nat.fib 3 = 2 from by simp [Nat.fib], Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    rw [exactWeightCount_zero_zero, exactWeightCount_zero_succ]; simp
  | succ m ih =>
    rw [exactWeightCollision_succ, ih, Finset.sum_range_succ]; ring


-- ══════════════════════════════════════════════════════════════
-- Cross-correlation at shift d
-- ══════════════════════════════════════════════════════════════

/-- Cross-correlation at shift d.
    def:pom-crossCorr -/
def crossCorr (m d : Nat) : Nat :=
  ∑ n ∈ Finset.range (Nat.fib (m + 3)),
    exactWeightCount m n * exactWeightCount m (n + d)

/-- C_0(m) = E(0,0)(m).
    thm:pom-crossCorr-zero -/
theorem crossCorr_zero_eq (m : Nat) :
    crossCorr m 0 = exactWeightCollision m := by
  simp [crossCorr, exactWeightCollision, sq]

-- ══════════════════════════════════════════════════════════════
-- E(0,1) = crossCorr(F_{m+2}) + crossCorr(F_{m+1})
-- ══════════════════════════════════════════════════════════════

/-- E(0,1) = crossCorr(F) + crossCorr(F-1).
    thm:pom-e01-crossCorr -/
theorem collision_cross_eq_two_crossCorr (m : Nat) :
    (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 % Nat.fib (m + 3) =
      (weight p.2 + Nat.fib (m + 2)) % Nat.fib (m + 3))).card =
    crossCorr m (Nat.fib (m + 2)) + crossCorr m (Nat.fib (m + 1)) := by
  classical
  -- Since weight < F_{m+3}, weight % F_{m+3} = weight. So LHS condition is:
  -- weight v1 = (weight v2 + F_{m+2}) % F_{m+3}
  -- Since weight v2 < F_{m+3}, weight v2 + F_{m+2} < F_{m+3} + F_{m+2} = F_{m+4} < 2·F_{m+3}
  -- So (weight v2 + F_{m+2}) % F_{m+3} = weight v2 + F_{m+2} if v2+F_{m+2} < F_{m+3}
  --                                     = weight v2 + F_{m+2} - F_{m+3} if v2+F_{m+2} ≥ F_{m+3}
  -- Case 1: v2 < F_{m+1} → v2+F_{m+2} < F_{m+3} → condition: v1 = v2 + F_{m+2}
  -- Case 2: v2 ≥ F_{m+1} → v2+F_{m+2} ≥ F_{m+3} → condition: v1 = v2 - F_{m+1}
  --   (since v2+F2 - F3 = v2 - F1, using F3 = F1+F2)
  have hFib3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  have hmod_id : ∀ v : Word m, weight v % Nat.fib (m + 3) = weight v := by
    intro v; exact Nat.mod_eq_of_lt (X.weight_lt_fib v)
  simp_rw [hmod_id]
  -- Split by whether weight v2 < F_{m+1}
  have hsplit : Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 = (weight p.2 + Nat.fib (m + 2)) % Nat.fib (m + 3)) =
      Finset.univ.filter (fun p : Word m × Word m =>
        weight p.1 = weight p.2 + Nat.fib (m + 2) ∧ weight p.2 < Nat.fib (m + 1)) ∪
      Finset.univ.filter (fun p : Word m × Word m =>
        weight p.1 + Nat.fib (m + 1) = weight p.2 ∧ Nat.fib (m + 1) ≤ weight p.2) := by
    ext ⟨v1, v2⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h
      by_cases hlt : weight v2 < Nat.fib (m + 1)
      · left; refine ⟨?_, hlt⟩
        have : weight v2 + Nat.fib (m + 2) < Nat.fib (m + 3) := by omega
        rwa [Nat.mod_eq_of_lt this] at h
      · right; push_neg at hlt; refine ⟨?_, hlt⟩
        have hge : Nat.fib (m + 3) ≤ weight v2 + Nat.fib (m + 2) := by omega
        have hlt2 : weight v2 + Nat.fib (m + 2) < 2 * Nat.fib (m + 3) := by
          have := X.weight_lt_fib v2; omega
        have hsub : weight v2 + Nat.fib (m + 2) - Nat.fib (m + 3) = weight v2 - Nat.fib (m + 1) := by omega
        rw [show weight v2 + Nat.fib (m + 2) = (weight v2 + Nat.fib (m + 2) - Nat.fib (m + 3)) +
          1 * Nat.fib (m + 3) from by omega, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt (by omega)] at h
        omega
    · rintro (⟨h, hlt⟩ | ⟨h, hge⟩)
      · rw [h, Nat.mod_eq_of_lt (by omega)]
      · have : weight v2 + Nat.fib (m + 2) = weight v1 + 1 * Nat.fib (m + 3) := by omega
        rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (X.weight_lt_fib v1)]
  have hdisj : Disjoint
      (Finset.univ.filter (fun p : Word m × Word m =>
        weight p.1 = weight p.2 + Nat.fib (m + 2) ∧ weight p.2 < Nat.fib (m + 1)))
      (Finset.univ.filter (fun p : Word m × Word m =>
        weight p.1 + Nat.fib (m + 1) = weight p.2 ∧ Nat.fib (m + 1) ≤ weight p.2)) := by
    apply Finset.disjoint_filter.mpr
    intro ⟨v1, v2⟩ _ ⟨h1, h2⟩ ⟨h3, _⟩; omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  -- Term 1: |{v1 = v2+F2, v2 < F1}| = crossCorr(m, F2)
  -- = Σ_n ewc(n)·ewc(n+F2) summed over n < F3, but only nonzero when n < F1
  -- (since ewc(n+F2)=0 when n+F2 ≥ F3, i.e. n ≥ F1)
  -- So = Σ_{n<F1} ewc(n)·ewc(n+F2) = Σ_{n<F3} ewc(n)·ewc(n+F2) = crossCorr(m,F2)
  -- The extra terms n ∈ [F1, F3) contribute 0 since ewc(n+F2)=0 for n≥F1.
  congr 1
  · -- Term 1 = crossCorr(m, F2)
    -- {(v1,v2): wt v1 = wt v2 + F2, wt v2 < F1}
    -- = ⊔_n ({wt=n+F2} ×ˢ {wt=n}) for n < F3
    -- = Σ_n ewc(n+F2)·ewc(n) = Σ_n ewc(n)·ewc(n+F2) = crossCorr(m,F2)
    -- |{(v1,v2): wt v1 = wt v2 + F2, wt v2 < F1}|
    -- = Σ_n |{v1:wt=n+F2}|·|{v2:wt=n}| (setting n=wt v2)
    -- = Σ_n ewc(n+F2)·ewc(n) = Σ_n ewc(n)·ewc(n+F2) = crossCorr(m,F2)
    unfold crossCorr exactWeightCount
    -- Commute: ewc(n)*ewc(n+F2) → ewc(n+F2)*ewc(n)
    rw [Finset.sum_congr rfl (fun n _ => Nat.mul_comm
      (Finset.univ.filter (fun w : Word m => weight w = n)).card
      (Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 2))).card)]
    symm; simp_rw [← Finset.card_product]
    rw [← Finset.card_biUnion]
    · congr 1; ext ⟨v1, v2⟩
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_product, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨n, _, h1, h2⟩
        have := X.weight_lt_fib v1
        exact ⟨by omega, by omega⟩
      · intro ⟨h, hlt⟩
        exact ⟨weight v2, X.weight_lt_fib v2, by omega, rfl⟩
    · intro n _ n' _ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_filter,
        Finset.mem_univ, true_and]
      intro ⟨_, v2⟩ ⟨_, h2⟩ ⟨_, h2'⟩; exact hne (h2.symm.trans h2')
  · -- Term 2: |{v1+F1 = v2, v2 ≥ F1}| = crossCorr(m, F1)
    -- = Σ_n ewc(n)·ewc(n+F1)
    -- This equals |{v1+F1 = v2}| since the extra condition v2≥F1 is automatic from v2=v1+F1≥F1
    -- (since weight ≥ 0)
    have hstrip : (Finset.univ.filter (fun p : Word m × Word m =>
        weight p.1 + Nat.fib (m + 1) = weight p.2 ∧ Nat.fib (m + 1) ≤ weight p.2)).card =
        (Finset.univ.filter (fun p : Word m × Word m =>
          weight p.1 + Nat.fib (m + 1) = weight p.2)).card := by
      congr 1; ext ⟨v1, v2⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, by omega⟩⟩
    rw [hstrip]
    -- |{v1+F1 = v2}| = crossCorr(m, F1)
    -- = Σ_n ewc(n+F1)·ewc(n) via change of variable
    -- This is the same pattern: Σ_n |{v1:wt=n}|·|{v2:wt=n+F1}| but we need v1+F1=v2
    -- i.e., v2=v1+F1, so Σ_n |{v2:wt=n+F1}|·|{v1:wt=n}| = crossCorr(m,F1)
    unfold crossCorr exactWeightCount
    symm; simp_rw [← Finset.card_product]
    rw [← Finset.card_biUnion]
    · congr 1; ext ⟨v1, v2⟩
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_product, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro ⟨n, hn, hv1, hv2⟩; omega
      · intro h; exact ⟨weight v1, X.weight_lt_fib v1, rfl, by omega⟩
    · intro n _ n' _ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_filter,
        Finset.mem_univ, true_and]
      intro ⟨v1, _⟩ ⟨h1, _⟩ ⟨h1', _⟩; exact hne (h1.symm.trans h1')

-- ══════════════════════════════════════════════════════════════
-- S_2(m+1) = 2E00 + 2·crossCorr(F) + 2·crossCorr(F-1)
-- ══════════════════════════════════════════════════════════════

/-- S_2(m+1) = 2·E00(m) + 2·crossCorr(m,F_{m+2}) + 2·crossCorr(m,F_{m+1}).
    thm:pom-s2-three-term -/
theorem momentSum_two_succ_three_term (m : Nat) :
    momentSum 2 (m + 1) =
    2 * exactWeightCollision m +
    2 * crossCorr m (Nat.fib (m + 2)) +
    2 * crossCorr m (Nat.fib (m + 1)) := by
  rw [momentSum_two_succ_two_term, collision_same_eq_exactWeightCollision,
      collision_cross_eq_two_crossCorr]; ring

-- ══════════════════════════════════════════════════════════════
-- crossCorr recurrence
-- ══════════════════════════════════════════════════════════════

/-- crossCorr(m+1, F_{m+2}) = 2·crossCorr(m, F_{m+2}) + E00(m).
    Derived from S_2 decomposition and exactWeightCollision_succ. -/
theorem crossCorr_fib_succ (m : Nat) :
    crossCorr (m + 1) (Nat.fib (m + 2)) =
    2 * crossCorr m (Nat.fib (m + 2)) + exactWeightCollision m := by
  -- From momentSum_two_succ_three_term:
  --   S_2(m+1) = 2·E00(m) + 2·crossCorr(m,F2) + 2·crossCorr(m,F1)
  -- From exactWeightCollision_succ: E00(m+1) = E00(m) + S_2(m)
  -- From momentSum_two_succ_three_term(m+1):
  --   S_2(m+2) = 2·E00(m+1) + 2·crossCorr(m+1,F3) + 2·crossCorr(m+1,F2)
  -- Also from collision_cross_eq_two_crossCorr:
  --   E01(m) = crossCorr(m,F2) + crossCorr(m,F1)
  -- From momentSum_two_succ_two_term:
  --   S_2(m+1) = 2·E00(m) + 2·E01(m) = 2·E00(m) + 2·(crossCorr(m,F2)+crossCorr(m,F1))
  -- And E00(m+1) = E00(m) + S_2(m) via 4-split showed:
  --   E00(m+1) = 2·E00(m) + 2·E01_pair(m) where E01_pair = crossCorr(m,F2)+crossCorr(m,F1)
  -- Wait, that's not what exactWeightCollision_succ showed. It showed
  --   E00(m+1) = E00(m) + S_2(m).
  -- And S_2(m) = 2·E00(m) + 2·(cc_F2 + cc_F1) - 2·E00(m) = ... no.
  -- Actually from h3term: S_2(m+1) = 2E00(m) + 2cc_F2(m) + 2cc_F1(m)
  -- From E00(m+1) = E00(m) + S_2(m)
  -- So S_2(m+1) = 2·E00(m) + 2·cc_F2(m) + 2·cc_F1(m)
  -- and E00(m+1) = E00(m) + S_2(m)
  -- We want: cc_F2(m+1) = 2·cc_F2(m) + E00(m)
  -- From h3term at m+1:
  --   S_2(m+2) = 2·E00(m+1) + 2·cc_{F3}(m+1) + 2·cc_{F2}(m+1)
  -- From exactWeightCollision_succ at m+1:
  --   E00(m+2) = E00(m+1) + S_2(m+1)
  -- This system has 2 unknowns: cc_{F3}(m+1) and cc_{F2}(m+1). Not enough.
  -- I need another equation. Let me use crossCorr_fib_succ at m+1 for F3:
  -- cc_{F3}(m+1) = crossCorr((m+1)+1, F_{(m+1)+2}) = crossCorr(m+2, F_{m+3})
  -- By the same theorem (at m+1): cc_{F3}(m+2) = 2·cc_{F3}(m+1) + E00(m+1)
  -- But this is circular since I'm trying to prove the theorem!
  --
  -- Let me just use the collision pair 4-split directly, same as exactWeightCollision_succ.
  -- crossCorr(m+1, F2) = |{(v1,v2) : wt v1 + F2 = wt v2 in Word(m+1)²}|
  -- Split by last bits → 4 terms. (ff)=cc(m,F2), (ft)=E00(m), (tf)=0, (tt)=cc(m,F2)
  -- But I can't easily get from the Finset.sum definition of crossCorr to the collision pair form
  -- without crossCorr_as_collision (which had the biUnion issue).
  --
  -- Let me try crossCorr_as_collision one more time with a different proof structure.
  classical
  have hcc_coll : ∀ m' d',
      crossCorr m' d' = (Finset.univ.filter (fun p : Word m' × Word m' =>
        weight p.1 + d' = weight p.2)).card := by
    intro m' d'
    unfold crossCorr exactWeightCount
    symm; simp_rw [← Finset.card_product]; rw [← Finset.card_biUnion]
    · congr 1; ext ⟨v1, v2⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        rw [Finset.mem_biUnion]
        exact ⟨weight v1, Finset.mem_range.mpr (X.weight_lt_fib v1),
          Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.symm⟩⟩⟩
      · intro h
        rw [Finset.mem_biUnion] at h
        obtain ⟨n, _, hp⟩ := h
        rw [Finset.mem_product] at hp
        have h1 := (Finset.mem_filter.mp hp.1).2
        have h2 := (Finset.mem_filter.mp hp.2).2
        linarith [h1, h2]
    · intro n _ n' _ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_filter,
        Finset.mem_univ, true_and]
      intro ⟨v1, _⟩ ⟨h1, _⟩ ⟨h1', _⟩; exact hne (h1.symm.trans h1')
  rw [hcc_coll (m + 1), ← collision_same_eq_exactWeightCollision m, hcc_coll m]
  -- 4-split
  have hmod_id : ∀ w : Word m, weight w % Nat.fib (m + 3) = weight w := by
    intro w; exact Nat.mod_eq_of_lt (X.weight_lt_fib w)
  have key : ∀ b1 b2 : Bool,
      (Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) =>
        weight p.1 + Nat.fib (m + 2) = weight p.2 ∧
        p.1 ⟨m, by omega⟩ = b1 ∧ p.2 ⟨m, by omega⟩ = b2)).card =
      (Finset.univ.filter (fun p : Word m × Word m =>
        weight p.1 + (if b1 then Nat.fib (m + 2) else 0) + Nat.fib (m + 2) =
        weight p.2 + (if b2 then Nat.fib (m + 2) else 0))).card := by
    intro b1 b2
    apply Finset.card_bij (fun (p : Word (m + 1) × Word (m + 1)) _ => (truncate p.1, truncate p.2))
    · intro ⟨w1, w2⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rw [weight, hp.2.1, weight, hp.2.2] at hp; exact hp.1
    · intro ⟨w1a, w2a⟩ ha ⟨w1b, w2b⟩ hb heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at ha hb heq ⊢
      exact ⟨by rw [← X.snoc_truncate_last w1a, ← X.snoc_truncate_last w1b, heq.1, ha.2.1, hb.2.1],
             by rw [← X.snoc_truncate_last w2a, ← X.snoc_truncate_last w2b, heq.2, ha.2.2, hb.2.2]⟩
    · intro ⟨v1, v2⟩ hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ⟨(snoc v1 b1, snoc v2 b2), ⟨by simp [weight_snoc]; exact hv, by simp, by simp⟩, by simp⟩
  have hdisj : ∀ b1 b2 b1' b2' : Bool, (b1, b2) ≠ (b1', b2') → Disjoint
      (Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) =>
        weight p.1 + Nat.fib (m + 2) = weight p.2 ∧ p.1 ⟨m, by omega⟩ = b1 ∧ p.2 ⟨m, by omega⟩ = b2))
      (Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) =>
        weight p.1 + Nat.fib (m + 2) = weight p.2 ∧ p.1 ⟨m, by omega⟩ = b1' ∧ p.2 ⟨m, by omega⟩ = b2')) := by
    intro b1 b2 b1' b2' hne; apply Finset.disjoint_filter.mpr
    intro ⟨w1, w2⟩ _ ⟨_, hb1, hb2⟩ ⟨_, hb1', hb2'⟩
    exact hne (Prod.ext (hb1.symm.trans hb1') (hb2.symm.trans hb2'))
  have hunion : Finset.univ.filter (fun p : Word (m + 1) × Word (m + 1) =>
      weight p.1 + Nat.fib (m + 2) = weight p.2) =
      Finset.univ.filter (fun p => weight p.1 + Nat.fib (m + 2) = weight p.2 ∧ p.1 ⟨m, by omega⟩ = false ∧ p.2 ⟨m, by omega⟩ = false) ∪
      Finset.univ.filter (fun p => weight p.1 + Nat.fib (m + 2) = weight p.2 ∧ p.1 ⟨m, by omega⟩ = false ∧ p.2 ⟨m, by omega⟩ = true) ∪
      Finset.univ.filter (fun p => weight p.1 + Nat.fib (m + 2) = weight p.2 ∧ p.1 ⟨m, by omega⟩ = true ∧ p.2 ⟨m, by omega⟩ = false) ∪
      Finset.univ.filter (fun p => weight p.1 + Nat.fib (m + 2) = weight p.2 ∧ p.1 ⟨m, by omega⟩ = true ∧ p.2 ⟨m, by omega⟩ = true) := by
    ext ⟨w1, w2⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h; rcases Bool.eq_false_or_eq_true (w1 ⟨m, by omega⟩) with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (w2 ⟨m, by omega⟩) with h2 | h2 <;> simp [h, h1, h2]
    · rintro (((⟨h, _, _⟩ | ⟨h, _, _⟩) | ⟨h, _, _⟩) | ⟨h, _, _⟩) <;> exact h
  rw [hunion]
  have dff_ft := hdisj false false false true (by decide)
  have dff_tf := hdisj false false true false (by decide)
  have dff_tt := hdisj false false true true (by decide)
  have dft_tf := hdisj false true true false (by decide)
  have dft_tt := hdisj false true true true (by decide)
  have dtf_tt := hdisj true false true true (by decide)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨dff_tt, dft_tt⟩, dtf_tt⟩),
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨dff_tf, dft_tf⟩),
    Finset.card_union_of_disjoint dff_ft,
    key false false, key false true, key true false, key true true]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  -- (ft): cancel F
  have hft : (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 + Nat.fib (m + 2) = weight p.2 + Nat.fib (m + 2))).card =
      (Finset.univ.filter (fun p : Word m × Word m =>
        weight p.1 % Nat.fib (m + 3) = weight p.2 % Nat.fib (m + 3))).card := by
    congr 1; ext ⟨v1, v2⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; rw [hmod_id, hmod_id]; omega
    · intro h; rw [hmod_id, hmod_id] at h; omega
  -- (tf): impossible
  have htf : (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 + Nat.fib (m + 2) + Nat.fib (m + 2) = weight p.2)).card = 0 := by
    apply Finset.card_eq_zero.mpr; rw [Finset.filter_eq_empty_iff]
    intro ⟨v1, v2⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro h
    have : weight v2 < Nat.fib (m + 3) := X.weight_lt_fib v2
    have : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
    have : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
    omega
  -- (tt): cancel one F
  have htt : (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 + Nat.fib (m + 2) + Nat.fib (m + 2) = weight p.2 + Nat.fib (m + 2))).card =
      (Finset.univ.filter (fun p : Word m × Word m =>
        weight p.1 + Nat.fib (m + 2) = weight p.2)).card := by
    congr 1; ext ⟨v1, v2⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  rw [hft, htf, htt]; omega


-- ══════════════════════════════════════════════════════════════
-- S_2 = E00 + 2·crossCorr(F)
-- ══════════════════════════════════════════════════════════════

private theorem crossCorr_as_collision' (m d : Nat) :
    crossCorr m d = (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 + d = weight p.2)).card := by
  classical
  unfold crossCorr exactWeightCount
  symm; simp_rw [← Finset.card_product]; rw [← Finset.card_biUnion]
  · congr 1; ext ⟨v1, v2⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; rw [Finset.mem_biUnion]
      exact ⟨weight v1, Finset.mem_range.mpr (X.weight_lt_fib v1),
        Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.symm⟩⟩⟩
    · intro h; rw [Finset.mem_biUnion] at h
      obtain ⟨n, _, hp⟩ := h; rw [Finset.mem_product] at hp
      have h1 := (Finset.mem_filter.mp hp.1).2
      have h2 := (Finset.mem_filter.mp hp.2).2
      linarith [h1, h2]
  · intro n _ n' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro ⟨v1, _⟩ ⟨h1, _⟩ ⟨h1', _⟩; exact hne (h1.symm.trans h1')

/-- S_2(m) = E00(m) + 2·crossCorr(m, F_{m+2}).
    thm:pom-s2-exact-crossCorr -/
theorem momentSum_two_eq_exact_plus_crossCorr (m : Nat) :
    momentSum 2 m = exactWeightCollision m + 2 * crossCorr m (Nat.fib (m + 2)) := by
  classical
  rw [momentSum_two_eq_collision, ← collision_same_eq_exactWeightCollision,
      crossCorr_as_collision']
  simp_rw [Fold_eq_iff_weight_mod]
  have hmod_id : ∀ v : Word m, weight v % Nat.fib (m + 3) = weight v := by
    intro v; exact Nat.mod_eq_of_lt (X.weight_lt_fib v)
  simp_rw [hmod_id]
  have hFpos : 0 < Nat.fib (m + 2) := fib_succ_pos (m + 1)
  have hlt2F : ∀ v : Word m, weight v < 2 * Nat.fib (m + 2) := by
    intro v
    have hf3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
    have hmono : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
    have hwt := X.weight_lt_fib v; omega
  have hsplit : Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 % Nat.fib (m + 2) = weight p.2 % Nat.fib (m + 2)) =
      Finset.univ.filter (fun p : Word m × Word m => weight p.1 = weight p.2) ∪
      Finset.univ.filter (fun p => weight p.1 = weight p.2 + Nat.fib (m + 2)) ∪
      Finset.univ.filter (fun p => weight p.1 + Nat.fib (m + 2) = weight p.2) := by
    ext ⟨v1, v2⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hmod
      have hdiv1 := Nat.div_add_mod (weight v1) (Nat.fib (m + 2))
      have hdiv2 := Nat.div_add_mod (weight v2) (Nat.fib (m + 2))
      have hq1 : weight v1 / Nat.fib (m + 2) < 2 := Nat.div_lt_of_lt_mul (by linarith [hlt2F v1])
      have hq2 : weight v2 / Nat.fib (m + 2) < 2 := Nat.div_lt_of_lt_mul (by linarith [hlt2F v2])
      rw [hmod] at hdiv1
      interval_cases (weight v1 / Nat.fib (m + 2)) <;>
        interval_cases (weight v2 / Nat.fib (m + 2)) <;> simp_all <;> omega
    · rintro ((h | h) | h)
      · rw [h]
      · rw [h, Nat.add_mod_right]
      · have : weight v2 = weight v1 + Nat.fib (m + 2) := by omega
        rw [this, Nat.add_mod_right]
  rw [hsplit,
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_filter.mpr (fun ⟨_, _⟩ _ h1 h2 => by omega),
       Finset.disjoint_filter.mpr (fun ⟨_, _⟩ _ h1 h2 => by omega)⟩),
    Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr (fun ⟨_, _⟩ _ h1 h2 => by omega))]
  have hswap : (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 = weight p.2 + Nat.fib (m + 2))).card =
      (Finset.univ.filter (fun p : Word m × Word m =>
        weight p.1 + Nat.fib (m + 2) = weight p.2)).card := by
    apply Finset.card_bij (fun (p : Word m × Word m) _ => (p.2, p.1))
    · intro ⟨v1, v2⟩ hv; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢; omega
    · intro _ _ _ _ h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
    · intro ⟨v1, v2⟩ hv; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ⟨(v2, v1), by simp; omega, rfl⟩
  rw [hswap]; ring

-- ══════════════════════════════════════════════════════════════
-- crossCorr(m+1, F) = S_2(m) — algebraic
-- ══════════════════════════════════════════════════════════════

/-- thm:pom-crossCorr-fib-prev -/
theorem crossCorr_fib_prev_eq_momentSum (m : Nat) :
    crossCorr (m + 1) (Nat.fib (m + 2)) = momentSum 2 m := by
  rw [crossCorr_fib_succ, momentSum_two_eq_exact_plus_crossCorr]; ring

-- ══════════════════════════════════════════════════════════════
-- S_2(m+2) expansion and UNCONDITIONAL RECURRENCE
-- ══════════════════════════════════════════════════════════════

/-- thm:pom-s2-expand -/
theorem momentSum_two_succ_succ_expand (m : Nat) :
    momentSum 2 (m + 2) =
    exactWeightCollision (m + 1) + momentSum 2 (m + 1) + 2 * momentSum 2 m := by
  rw [momentSum_two_succ_three_term (m + 1),
      show Nat.fib (m + 1 + 2) = Nat.fib (m + 3) from by ring_nf,
      show Nat.fib (m + 1 + 1) = Nat.fib (m + 2) from by ring_nf]
  -- 2·cc(m+1,F3) + E00(m+1) = S_2(m+1) [by crossCorr_fib_succ + crossCorr_fib_prev_eq_momentSum]
  have hcf3_sum : 2 * crossCorr (m + 1) (Nat.fib (m + 3)) + exactWeightCollision (m + 1) =
      momentSum 2 (m + 1) := by
    have h1 := crossCorr_fib_prev_eq_momentSum (m + 1)
    rw [show Nat.fib ((m + 1) + 2) = Nat.fib (m + 3) from by ring_nf] at h1
    have h2 := crossCorr_fib_succ (m + 1)
    rw [show Nat.fib ((m + 1) + 2) = Nat.fib (m + 3) from by ring_nf] at h2
    linarith
  rw [crossCorr_fib_prev_eq_momentSum]; linarith

/-- S_2(m+3) + 2·S_2(m) = 2·S_2(m+2) + 2·S_2(m+1). UNCONDITIONAL.
    prop:pom-s2-recurrence -/
theorem momentSum_two_recurrence (m : Nat) :
    momentSum 2 (m + 3) + 2 * momentSum 2 m =
    2 * momentSum 2 (m + 2) + 2 * momentSum 2 (m + 1) := by
  have h1 := momentSum_two_succ_succ_expand m
  have h2 := momentSum_two_succ_succ_expand (m + 1)
  have h3 := exactWeightCollision_succ (m + 1)
  linarith

/-- E00 satisfies the S_2 three-step recurrence.
    bridge:e00-recurrence -/
theorem exactWeightCollision_recurrence (m : Nat) :
    exactWeightCollision (m + 3) + 2 * exactWeightCollision m =
    2 * exactWeightCollision (m + 2) + 2 * exactWeightCollision (m + 1) := by
  induction m with
  | zero => native_decide
  | succ m ih =>
    show exactWeightCollision (m + 4) + 2 * exactWeightCollision (m + 1) =
        2 * exactWeightCollision (m + 3) + 2 * exactWeightCollision (m + 2)
    have es0 := exactWeightCollision_succ m
    have es1 : exactWeightCollision (m + 2) = exactWeightCollision (m + 1) +
        momentSum 2 (m + 1) := by have := exactWeightCollision_succ (m + 1); linarith
    have es2 : exactWeightCollision (m + 3) = exactWeightCollision (m + 2) +
        momentSum 2 (m + 2) := by have := exactWeightCollision_succ (m + 2); linarith
    have es3 : exactWeightCollision (m + 4) = exactWeightCollision (m + 3) +
        momentSum 2 (m + 3) := by have := exactWeightCollision_succ (m + 3); linarith
    have sr := momentSum_two_recurrence m
    linarith

-- ══════════════════════════════════════════════════════════════
-- Phase 228: E00 Cauchy-Schwarz + crossCorr bound
-- ══════════════════════════════════════════════════════════════

/-- E00(m) * F(m+3) ≥ 4^m (Cauchy-Schwarz on ewc). thm:pom-s2-exact-crossCorr -/
theorem exactWeightCollision_cauchy_schwarz (m : Nat) :
    4 ^ m ≤ exactWeightCollision m * Nat.fib (m + 3) := by
  -- Cauchy-Schwarz: (Σ f)² ≤ |S| * Σ f²
  -- Here f = ewc, S = range(F(m+3)), Σ ewc = 2^m, Σ ewc² = E00
  have hCS : (∑ n ∈ Finset.range (Nat.fib (m + 3)), exactWeightCount m n) ^ 2 ≤
      (Finset.range (Nat.fib (m + 3))).card *
      ∑ n ∈ Finset.range (Nat.fib (m + 3)), exactWeightCount m n ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [exactWeightCount_sum, Finset.card_range] at hCS
  rw [show 4 = 2 * 2 from rfl, Nat.mul_pow, show (2 ^ m) * (2 ^ m) = (2 ^ m) ^ 2 from by ring]
  calc (2 ^ m) ^ 2 ≤ Nat.fib (m + 3) * exactWeightCollision m := hCS
    _ = exactWeightCollision m * Nat.fib (m + 3) := Nat.mul_comm _ _

/-- Shifted ewc² sum is bounded by E00. -/
private theorem shifted_ewc_sq_le (m d : Nat) :
    ∑ n ∈ Finset.range (Nat.fib (m + 3)), exactWeightCount m (n + d) ^ 2 ≤
    exactWeightCollision m := by
  unfold exactWeightCollision
  -- Split into terms where n+d < F(m+3) (contribute to E00) and n+d ≥ F(m+3) (contribute 0)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (Nat.fib (m + 3)))
    (fun n => n + d < Nat.fib (m + 3))]
  -- The "out of range" terms are all zero
  have hzero : ∑ n ∈ (Finset.range (Nat.fib (m + 3))).filter
      (fun n => ¬(n + d < Nat.fib (m + 3))),
      exactWeightCount m (n + d) ^ 2 = 0 := by
    apply Finset.sum_eq_zero; intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    rw [exactWeightCount_eq_zero_of_ge_fib m (n + d) (by omega)]; simp
  rw [hzero, Nat.add_zero]
  -- The "in range" terms inject into the full E00 sum
  let S := (Finset.range (Nat.fib (m + 3))).filter (fun n => n + d < Nat.fib (m + 3))
  let T := Finset.range (Nat.fib (m + 3))
  -- Map n ↦ n+d sends S injectively into T
  calc ∑ n ∈ S, exactWeightCount m (n + d) ^ 2
      = ∑ n ∈ S.image (· + d), exactWeightCount m n ^ 2 := by
        rw [Finset.sum_image]; intro n₁ _ n₂ _ h; simp only [Nat.add_right_cancel_iff] at h; exact h
    _ ≤ ∑ n ∈ T, exactWeightCount m n ^ 2 := by
        apply Finset.sum_le_sum_of_subset
        intro k hk; simp only [S, T, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hk ⊢
        obtain ⟨n, hn, rfl⟩ := hk; exact hn.2

/-- C(m,d) ≤ E00(m). thm:pom-s2-exact-crossCorr -/
theorem crossCorr_le_exactWeightCollision (m d : Nat) :
    crossCorr m d ≤ exactWeightCollision m := by
  -- AM-GM: 2*a*b ≤ a² + b², so 2*C ≤ Σ(ewc(n)² + ewc(n+d)²) = E00 + shifted_E00 ≤ 2*E00
  -- Hence C ≤ E00
  suffices h : 2 * crossCorr m d ≤ 2 * exactWeightCollision m by omega
  calc 2 * crossCorr m d
      = 2 * ∑ n ∈ Finset.range (Nat.fib (m + 3)),
          exactWeightCount m n * exactWeightCount m (n + d) := rfl
    _ = ∑ n ∈ Finset.range (Nat.fib (m + 3)),
          2 * (exactWeightCount m n * exactWeightCount m (n + d)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ n ∈ Finset.range (Nat.fib (m + 3)),
          (exactWeightCount m n ^ 2 + exactWeightCount m (n + d) ^ 2) := by
        apply Finset.sum_le_sum; intro n _
        -- 2ab ≤ a² + b² (cast to ℤ then nlinarith on (a-b)² ≥ 0)
        have : (2 * (exactWeightCount m n * exactWeightCount m (n + d)) : ℤ) ≤
            (exactWeightCount m n ^ 2 + exactWeightCount m (n + d) ^ 2 : ℤ) := by
          nlinarith [sq_nonneg ((exactWeightCount m n : ℤ) - exactWeightCount m (n + d))]
        exact_mod_cast this
    _ = (∑ n ∈ Finset.range (Nat.fib (m + 3)), exactWeightCount m n ^ 2) +
        (∑ n ∈ Finset.range (Nat.fib (m + 3)), exactWeightCount m (n + d) ^ 2) :=
        Finset.sum_add_distrib
    _ ≤ exactWeightCollision m + exactWeightCollision m := by
        apply Nat.add_le_add
        · exact le_refl _
        · exact shifted_ewc_sq_le m d
    _ = 2 * exactWeightCollision m := by ring

-- ══════════════════════════════════════════════════════════════
-- Phase R8: cross-term = cwc bridge + S2 decomposition
-- ══════════════════════════════════════════════════════════════

/-- crossWeightCorrelation = crossCorr at shift F_{m+2}. -/
theorem crossWeightCorrelation_eq_crossCorr (m : Nat) :
    crossWeightCorrelation m = crossCorr m (Nat.fib (m + 2)) := by
  unfold crossWeightCorrelation crossCorr
  -- range(F_{m+2}) vs range(F_{m+3}): extra terms for n ≥ F_{m+2} are zero
  symm
  rw [show Nat.fib (m + 3) = Nat.fib (m + 2) + Nat.fib (m + 1) from by
    rw [Nat.fib_add_two]; ring]
  rw [Finset.sum_range_add]
  suffices h : ∑ i ∈ Finset.range (Nat.fib (m + 1)),
      exactWeightCount m (Nat.fib (m + 2) + i) *
      exactWeightCount m (Nat.fib (m + 2) + i + Nat.fib (m + 2)) = 0 by omega
  apply Finset.sum_eq_zero
  intro i hi
  have him1 : i < Nat.fib (m + 1) := Finset.mem_range.mp hi
  have hge : Nat.fib (m + 3) ≤ Nat.fib (m + 2) + i + Nat.fib (m + 2) := by
    have hfib3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
    linarith [Nat.fib_mono (show m + 1 ≤ m + 2 from by omega)]
  rw [exactWeightCount_eq_zero_of_ge_fib m _ hge, Nat.mul_zero]

/-- ∑_x d_0(x)·d_1(x) = crossWeightCorrelation m.
    prop:pom-hiddenbit-mixed-moment-cluster -/
theorem fiberHiddenBitCount_cross_eq_cwc (m : Nat) :
    ∑ x : X m, fiberHiddenBitCount 0 x * fiberHiddenBitCount 1 x =
    crossWeightCorrelation m := by
  simp_rw [fiberHiddenBitCount_zero_eq_ewc, fiberHiddenBitCount_one_eq_ewc]
  unfold crossWeightCorrelation
  have hbij := X.stableValueFin_bijective m
  have step : ∑ x : X m, exactWeightCount m (stableValue x) *
      exactWeightCount m (stableValue x + Nat.fib (m + 2)) =
      ∑ r : Fin (Nat.fib (m + 2)), exactWeightCount m r.val *
        exactWeightCount m (r.val + Nat.fib (m + 2)) := by
    rw [show (fun x : X m => exactWeightCount m (stableValue x) *
        exactWeightCount m (stableValue x + Nat.fib (m + 2))) =
      (fun r : Fin (Nat.fib (m + 2)) => exactWeightCount m r.val *
        exactWeightCount m (r.val + Nat.fib (m + 2))) ∘
      X.stableValueFin from by ext x; simp [X.stableValueFin]]
    exact hbij.sum_comp (fun r : Fin (Nat.fib (m + 2)) => exactWeightCount m r.val *
      exactWeightCount m (r.val + Nat.fib (m + 2)))
  rw [step, ← Fin.sum_univ_eq_sum_range (n := Nat.fib (m + 2))
    (f := fun n => exactWeightCount m n * exactWeightCount m (n + Nat.fib (m + 2)))]

/-- S_2(m) = E00(m) + 2·cwc(m).
    thm:pom-s2-exact-crossCorr -/
theorem momentSum_two_eq_E00_add_cwc (m : Nat) :
    momentSum 2 m = exactWeightCollision m + 2 * crossWeightCorrelation m := by
  rw [crossWeightCorrelation_eq_crossCorr, momentSum_two_eq_exact_plus_crossCorr]

/-- S_2(m+2) = E00(m+2) + 2·S_2(m). -/
private theorem momentSum_two_eq_E00_add_two_S (m : Nat) :
    momentSum 2 (m + 2) = exactWeightCollision (m + 2) + 2 * momentSum 2 m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 =>
      rw [momentSum_two_two, momentSum_two_zero]
      show 6 = exactWeightCollision 2 + 2
      rw [exactWeightCollision_eq_sum]; simp [Finset.sum_range_succ, momentSum_two_zero,
        momentSum_two_one]
    | 1 =>
      rw [momentSum_two_three, momentSum_two_one]
      show 14 = exactWeightCollision 3 + 4
      rw [exactWeightCollision_eq_sum]; simp [Finset.sum_range_succ, momentSum_two_zero,
        momentSum_two_one, momentSum_two_two]
    | m + 2 =>
      have hrec := momentSum_two_recurrence (m + 1)
      -- hrec: S_2(m+4) + 2*S_2(m+1) = 2*S_2(m+3) + 2*S_2(m+2)
      have hE := exactWeightCollision_succ (m + 3)
      -- hE: E00(m+4) = E00(m+3) + S_2(m+3)
      have hprev := ih (m + 1) (by omega)
      -- hprev: S_2(m+3) = E00(m+3) + 2*S_2(m+1)
      linarith

/-- cwc(m+2) = S_2(m). Algebraic proof.
    thm:pom-hiddenbit-jump-collision-isomorphism -/
theorem crossWeightCorrelation_eq_momentSum_two (m : Nat) :
    crossWeightCorrelation (m + 2) = momentSum 2 m := by
  have h1 := momentSum_two_eq_E00_add_cwc (m + 2)
  have h2 := momentSum_two_eq_E00_add_two_S m
  omega

/-- 4·S_2(m) ≤ S_2(m+2).
    thm:pom-hiddenbit-bias-energy-identity -/
theorem momentSum_two_quadruple_le (m : Nat) :
    4 * momentSum 2 m ≤ momentSum 2 (m + 2) := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => rw [momentSum_two_zero, momentSum_two_two]; omega
    | 1 => rw [momentSum_two_one, momentSum_two_three]; omega
    | m + 2 =>
      -- Use recurrences to relate S_2(m+4) to earlier values
      have hrec_m := momentSum_two_recurrence m
      have hrec_m1 := momentSum_two_recurrence (m + 1)
      have ih0 := ih m (by omega)
      have ih1 := ih (m + 1) (by omega)
      -- Normalize: m+1+3 = m+4, m+1+2 = m+3, m+1+1 = m+2, m+2+2 = m+4
      show 4 * momentSum 2 (m + 2) ≤ momentSum 2 (m + 4)
      -- From hrec_m1: S(m+4) + 2S(m+1) = 2S(m+3) + 2S(m+2)
      -- From hrec_m: S(m+3) + 2S(m) = 2S(m+2) + 2S(m+1)
      -- So S(m+3) = 2S(m+2) + 2S(m+1) - 2S(m) ≥ 2S(m+2) (since ih0: S(m+2) ≥ 4S(m) ≥ 2S(m+1)... no)
      -- S(m+4) = 2S(m+3) + 2S(m+2) - 2S(m+1)
      -- Need: 4S(m+2) ≤ 2S(m+3) + 2S(m+2) - 2S(m+1)
      -- i.e. 2S(m+2) + 2S(m+1) ≤ 2S(m+3) = 2*(2S(m+2) + 2S(m+1) - 2S(m))
      -- i.e. 2S(m+2) + 2S(m+1) ≤ 4S(m+2) + 4S(m+1) - 4S(m)
      -- i.e. 4S(m) ≤ 2S(m+2) + 2S(m+1), which follows from ih0: 4S(m) ≤ S(m+2)
      linarith

-- ══════════════════════════════════════════════════════════════
-- Phase R10: hidden-bit bias energy
-- ══════════════════════════════════════════════════════════════

/-- Hidden-bit bias energy (Int version):
    ∑ (↑d_0 - ↑d_1)² = ↑S_2(m+2) - 4·↑S_2(m).
    thm:pom-hiddenbit-bias-energy-identity -/
theorem hiddenBitBiasEnergy_int (m : Nat) :
    ∑ x : X (m + 2),
      ((fiberHiddenBitCount 0 x : Int) - fiberHiddenBitCount 1 x) ^ 2 =
    (momentSum 2 (m + 2) : Int) - 4 * momentSum 2 m := by
  -- (a-b)^2 + 4ab = (a+b)^2 in ℤ, rearranged
  have hcross := fiberHiddenBitCount_cross_eq_cwc (m + 2)
  have hcwc := crossWeightCorrelation_eq_momentSum_two m
  -- Rewrite: ∑(a-b)² = ∑(a+b)² - 4·∑(ab) using Int arithmetic
  -- Step 1: ∑(a-b)² + 4·∑(ab) = ∑(a+b)² (pointwise (a-b)²+4ab=(a+b)²)
  have hadd : ∑ x : X (m + 2),
      ((fiberHiddenBitCount 0 x : Int) - fiberHiddenBitCount 1 x) ^ 2 +
      4 * ∑ x : X (m + 2), ((fiberHiddenBitCount 0 x : Int) * fiberHiddenBitCount 1 x) =
      ∑ x : X (m + 2), (X.fiberMultiplicity x : Int) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1; ext x
    have hsplit := fiberMultiplicity_split_by_hiddenBit x
    push_cast [hsplit]; ring
  -- Step 2: ∑ d² = S_2 and ∑ d_0·d_1 = S_2(m) in ℤ
  -- ∑ ↑(fM x)^2 = ↑(∑ fM(x)^2) = ↑S_2
  have hS : (∑ x : X (m + 2), (X.fiberMultiplicity x : Int) ^ 2) =
      (momentSum 2 (m + 2) : Int) := by
    norm_cast
  have hP : (∑ x : X (m + 2), (fiberHiddenBitCount 0 x : Int) * fiberHiddenBitCount 1 x) =
      (momentSum 2 m : Int) := by norm_cast; exact hcross.trans hcwc
  linarith

/-- E00(m+2) = S_2(m+2) - 2·S_2(m).
    thm:pom-e00-telescoping -/
theorem exactWeightCollision_eq_S2_sub (m : Nat) :
    exactWeightCollision (m + 2) = momentSum 2 (m + 2) - 2 * momentSum 2 m := by
  have h := momentSum_two_eq_E00_add_two_S m
  have h4 := momentSum_two_quadruple_le m
  omega

/-- cwc(m) > 0 for m ≥ 2.
    def:pom-crossWeightCorrelation -/
theorem crossWeightCorrelation_pos (m : Nat) (hm : 2 ≤ m) :
    0 < crossWeightCorrelation m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [crossWeightCorrelation_eq_momentSum_two]
  -- S_2(k) ≥ E00(k) ≥ 1
  have hdecomp := momentSum_two_eq_E00_add_cwc k
  have hEpos : 0 < exactWeightCollision k := by
    rw [exactWeightCollision_eq_sum]; omega
  omega

end Omega
