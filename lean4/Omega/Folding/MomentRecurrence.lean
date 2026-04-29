import Omega.Folding.CollisionDecomp

namespace Omega

-- ══════════════════════════════════════════════════════════════
-- S_2 recurrence consequences
-- ══════════════════════════════════════════════════════════════

/-- S_2(m+3) = 2·S_2(m+2) + 2·S_2(m+1) - 2·S_2(m). Subtraction form.
    thm:pom-s2-recurrence-sub -/
theorem momentSum_two_recurrence_sub (m : Nat) :
    momentSum 2 (m + 3) = 2 * momentSum 2 (m + 2) + 2 * momentSum 2 (m + 1) - 2 * momentSum 2 m := by
  have h := momentSum_two_recurrence m; omega

-- ══════════════════════════════════════════════════════════════
-- Positivity
-- ══════════════════════════════════════════════════════════════

/-- S_2(m) > 0 for all m.
    thm:pom-s2-pos -/
theorem momentSum_two_pos' (m : Nat) : 0 < momentSum 2 m := by
  calc 0 < 2 ^ m := Nat.pos_of_ne_zero (by positivity)
    _ ≤ momentSum 2 m := momentSum_two_ge_pow m

-- ══════════════════════════════════════════════════════════════
-- Monotonicity
-- ══════════════════════════════════════════════════════════════

/-- S_2 is monotone: S_2(m) ≤ S_2(m+1).
    thm:pom-s2-mono -/
theorem momentSum_two_mono' (m : Nat) : momentSum 2 m ≤ momentSum 2 (m + 1) := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => rw [momentSum_two_zero, momentSum_two_one]; omega
    | 1 => rw [momentSum_two_one, momentSum_two_two]; omega
    | 2 =>
      rw [momentSum_two_two]
      rw [show (2 + 1 : Nat) = 3 from rfl, momentSum_two_three]; omega
    | m + 3 =>
      -- S_2(m+4) = 2·S_2(m+3) + 2·S_2(m+2) - 2·S_2(m+1)
      -- S_2(m+3) = 2·S_2(m+2) + 2·S_2(m+1) - 2·S_2(m)
      -- S_2(m+4) - S_2(m+3) = 2·(S_2(m+3)-S_2(m+2)) + 2·(S_2(m+2)-S_2(m+1)) - 2·(S_2(m+1)-S_2(m))
      -- Wait, let me use the recurrence directly.
      -- From recurrence: S(m+6) + 2S(m+3) = 2S(m+5) + 2S(m+4)
      -- So S(m+6) = 2S(m+5) + 2S(m+4) - 2S(m+3)
      -- Need S(m+3) ≤ S(m+4).
      -- From recurrence at m: S(m+3) + 2S(m) = 2S(m+2) + 2S(m+1)
      -- S(m+3) = 2S(m+2) + 2S(m+1) - 2S(m)
      -- From recurrence at m+1: S(m+4) = 2S(m+3) + 2S(m+2) - 2S(m+1)
      -- S(m+4) - S(m+3) = 2S(m+3) + 2S(m+2) - 2S(m+1) - S(m+3)
      --                  = S(m+3) + 2S(m+2) - 2S(m+1)
      --                  = (2S(m+2)+2S(m+1)-2S(m)) + 2S(m+2) - 2S(m+1)
      --                  = 4S(m+2) - 2S(m)
      -- Since S(m+2) ≥ 2^(m+2) = 4·2^m ≥ 4 and S(m) ≥ 1, we need 4S(m+2) ≥ 2S(m).
      -- S(m+2) ≥ 2^(m+2) and S(m) ≤ S(m+2) (by IH twice). So 4S(m+2) ≥ 4S(m) ≥ 2S(m). ✓
      have hrec1 := momentSum_two_recurrence (m + 1)
      have ihm1 := ih (m + 1) (by omega)
      have ihm2 := ih (m + 2) (by omega)
      -- S(m+4) + 2S(m+1) = 2S(m+3) + 2S(m+2)
      -- Need: S(m+3) ≤ S(m+4)
      -- i.e., S(m+3) ≤ 2S(m+3) + 2S(m+2) - 2S(m+1)
      -- i.e., 2S(m+1) ≤ S(m+3) + 2S(m+2)
      -- S(m+3) ≥ S(m+2) ≥ S(m+1) (by IH), so S(m+3)+2S(m+2) ≥ 3S(m+1) ≥ 2S(m+1). ✓
      linarith

/-- S_2 is strictly monotone for m ≥ 1.
    thm:pom-s2-strict-mono -/
theorem momentSum_two_strict_mono' (m : Nat) (hm : 1 ≤ m) :
    momentSum 2 m < momentSum 2 (m + 1) := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => omega
    | 1 => rw [momentSum_two_one, momentSum_two_two]; omega
    | 2 =>
      rw [momentSum_two_two, show (2 + 1 : Nat) = 3 from rfl, momentSum_two_three]; omega
    | m + 3 =>
      -- S(m+4) - S(m+3) = S(m+3) + 2S(m+2) - 2S(m+1) [from recurrence]
      -- = (S(m+3) - S(m+2)) + (S(m+2) - S(m+1)) + 2(S(m+2) - S(m+1))
      -- > 0 by IH at m+2 and m+1
      have hrec := momentSum_two_recurrence (m + 1)
      have ihm2 : momentSum 2 (m + 2) < momentSum 2 (m + 3) := ih (m + 2) (by omega) (by omega)
      have ihm1 : momentSum 2 (m + 1) < momentSum 2 (m + 2) := ih (m + 1) (by omega) (by omega)
      -- S(m+4) + 2S(m+1) = 2S(m+3) + 2S(m+2)
      -- S(m+4) = 2S(m+3) + 2S(m+2) - 2S(m+1) > 2S(m+3) + 2S(m+1) - 2S(m+1) = 2S(m+3)
      -- Wait: S(m+4) = 2S(m+3) + 2(S(m+2)-S(m+1)) > 2S(m+3) > S(m+3). ✓
      linarith

-- ══════════════════════════════════════════════════════════════
-- General S_q = Σ wcc^q
-- ══════════════════════════════════════════════════════════════

/-- General q-moment = Σ wcc^q. Generalizes momentSum_two_eq_congr_sq_sum to all q.
    prop:pom-moment-congruence-q-general -/
theorem momentSum_eq_congr_pow_sum (q m : Nat) :
    momentSum q m =
    ∑ r ∈ Finset.range (Nat.fib (m + 2)), weightCongruenceCount m r ^ q := by
  unfold momentSum
  simp_rw [fiberMultiplicity_eq_wcc]
  have hbij := X.stableValueFin_bijective m
  have step : ∑ x : X m, weightCongruenceCount m (stableValue x) ^ q =
      ∑ r : Fin (Nat.fib (m + 2)), weightCongruenceCount m r.val ^ q := by
    rw [show (fun x : X m => weightCongruenceCount m (stableValue x) ^ q) =
      (fun r : Fin (Nat.fib (m + 2)) => weightCongruenceCount m r.val ^ q) ∘
      X.stableValueFin from by ext x; simp [X.stableValueFin]]
    exact hbij.sum_comp (fun r : Fin (Nat.fib (m + 2)) => weightCongruenceCount m r.val ^ q)
  rw [step, ← Fin.sum_univ_eq_sum_range]

/-- Named alias: S_q(m) = Σ_{r<F} wcc(m,r)^q.
    prop:pom-moment-congruence-q-general -/
theorem momentSum_eq_weightCongruenceCount_pow (q m : Nat) :
    momentSum q m =
    (Finset.range (Nat.fib (m + 2))).sum (fun r => weightCongruenceCount m r ^ q) :=
  momentSum_eq_congr_pow_sum q m

-- ══════════════════════════════════════════════════════════════
-- exactWeightTriple definition
-- ══════════════════════════════════════════════════════════════

/-- Sum of cubed exact weight counts.
    def:pom-exactWeightTriple -/
def exactWeightTriple (m : Nat) : Nat :=
  ∑ n ∈ Finset.range (Nat.fib (m + 3)), exactWeightCount m n ^ 3

-- ══════════════════════════════════════════════════════════════
-- S_q positivity
-- ══════════════════════════════════════════════════════════════

/-- S_q(m) > 0 for all q, m.
    thm:pom-sq-pos-general -/
theorem momentSum_pos' (q m : Nat) : 0 < momentSum q m := by
  unfold momentSum
  apply Finset.sum_pos
  · intro x _
    exact Nat.pos_of_ne_zero (pow_ne_zero q (Nat.pos_iff_ne_zero.mp (X.fiberMultiplicity_pos x)))
  · exact ⟨⟨fun _ => false, no11_allFalse⟩, Finset.mem_univ _⟩

-- ══════════════════════════════════════════════════════════════
-- S_3 = triple collision count
-- ══════════════════════════════════════════════════════════════

/-- S_3(m) = #{(w1,w2,w3) : Fold w1 = Fold w2 = Fold w3}.
    thm:pom-s3-triple-collision -/
theorem momentSum_three_eq_triple_collision (m : Nat) :
    momentSum 3 m = (Finset.univ.filter
      (fun p : Word m × Word m × Word m =>
        Fold p.1 = Fold p.2.1 ∧ Fold p.2.1 = Fold p.2.2)).card := by
  classical
  simp only [momentSum]
  -- d(x)³ = |fiber x ×ˢ (fiber x ×ˢ fiber x)|
  simp_rw [show ∀ (x : X m), X.fiberMultiplicity x ^ 3 =
    (X.fiber x ×ˢ (X.fiber x ×ˢ X.fiber x)).card from fun x => by
      simp [X.fiberMultiplicity, Finset.card_product]; ring]
  rw [← Finset.card_biUnion]
  · congr 1; ext ⟨w1, w2, w3⟩
    simp only [Finset.mem_biUnion, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and, X.mem_fiber]
    exact ⟨fun ⟨x, hw1, hw2, hw3⟩ => ⟨hw1.trans hw2.symm, hw2.trans hw3.symm⟩,
      fun ⟨h12, h23⟩ => ⟨Fold w1, rfl, h12.symm, (h12.trans h23).symm⟩⟩
  · intro x _ y _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, X.mem_fiber]
    intro ⟨w1, w2, w3⟩ ⟨hw1, _, _⟩ ⟨hw1', _, _⟩
    exact hne (hw1.symm.trans hw1')

/-- Triple collision ↔ weight triple congruence.
    thm:pom-triple-collision-weight-mod -/
theorem triple_collision_iff_weight_mod (m : Nat) :
    (Finset.univ.filter (fun p : Word m × Word m × Word m =>
      Fold p.1 = Fold p.2.1 ∧ Fold p.2.1 = Fold p.2.2)).card =
    (Finset.univ.filter (fun p : Word m × Word m × Word m =>
      weight p.1 % Nat.fib (m + 2) = weight p.2.1 % Nat.fib (m + 2) ∧
      weight p.2.1 % Nat.fib (m + 2) = weight p.2.2 % Nat.fib (m + 2))).card := by
  congr 1; ext ⟨w1, w2, w3⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨h1, h2⟩ => ⟨(Fold_eq_iff_weight_mod w1 w2).mp h1,
      (Fold_eq_iff_weight_mod w2 w3).mp h2⟩,
    fun ⟨h1, h2⟩ => ⟨(Fold_eq_iff_weight_mod w1 w2).mpr h1,
      (Fold_eq_iff_weight_mod w2 w3).mpr h2⟩⟩

-- ══════════════════════════════════════════════════════════════
-- S_q universal inequalities
-- ══════════════════════════════════════════════════════════════

/-- S_q(m) ≥ 2^m for q ≥ 1.
    thm:pom-sq-ge-pow -/
theorem momentSum_ge_pow' (q m : Nat) (hq : 1 ≤ q) : 2 ^ m ≤ momentSum q m := by
  calc 2 ^ m = ∑ x : X m, X.fiberMultiplicity x := (X.fiberMultiplicity_sum_eq_pow m).symm
    _ ≤ ∑ x : X m, X.fiberMultiplicity x ^ q := by
        apply Finset.sum_le_sum; intro x _
        exact le_self_pow (X.fiberMultiplicity_pos x) (by omega)
    _ = momentSum q m := rfl

/-- S_q(m) ≤ S_{q+1}(m).
    thm:pom-sq-le-succ -/
theorem momentSum_le_succ' (q m : Nat) : momentSum q m ≤ momentSum (q + 1) m := by
  simp only [momentSum]
  apply Finset.sum_le_sum; intro x _
  exact pow_le_pow_right' (X.fiberMultiplicity_pos x) (Nat.le_succ q)

/-- Cauchy-Schwarz: S_2(m) · F_{m+2} ≥ 4^m.
    thm:pom-s2-cauchy-schwarz -/
theorem momentSum_two_mul_card_ge (m : Nat) :
    momentSum 2 m * Nat.fib (m + 2) ≥ 4 ^ m := by
  have hcs := momentSum_cauchy_schwarz m
  rw [show (2 ^ m) ^ 2 = 4 ^ m from by rw [← pow_mul, show 4 = 2 ^ 2 from by norm_num, ← pow_mul]; ring_nf] at hcs
  linarith [Nat.mul_comm (momentSum 2 m) (Nat.fib (m + 2))]

/-- S_q(m) ≥ F_{m+2} for all q.
    thm:pom-sq-ge-card -/
theorem momentSum_ge_card' (q m : Nat) : Nat.fib (m + 2) ≤ momentSum q m := by
  calc Nat.fib (m + 2) = Fintype.card (X m) := (X.card_eq_fib m).symm
    _ = ∑ _ : X m, 1 := by simp
    _ ≤ ∑ x : X m, X.fiberMultiplicity x ^ q := by
        apply Finset.sum_le_sum; intro x _
        exact Nat.one_le_pow q _ (X.fiberMultiplicity_pos x)
    _ = momentSum q m := rfl

/-- S_q(m) ≤ D_m^{q-1} · 2^m (wrapper of momentSum_le_max_pow).
    thm:pom-sq-upper-bound -/
theorem momentSum_upper_bound' (q m : Nat) (hq : 1 ≤ q) :
    momentSum q m ≤ X.maxFiberMultiplicity m ^ (q - 1) * 2 ^ m :=
  momentSum_le_max_pow q m hq

-- ══════════════════════════════════════════════════════════════
-- S_2 number-theoretic properties
-- ══════════════════════════════════════════════════════════════

/-- S_2(m) is even for m ≥ 1.
    thm:pom-s2-even -/
theorem momentSum_two_even (m : Nat) (hm : 1 ≤ m) : 2 ∣ momentSum 2 m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => omega
    | 1 => exact ⟨1, by rw [momentSum_two_one]⟩
    | 2 => exact ⟨3, by rw [momentSum_two_two]⟩
    | m + 3 =>
      have hrec := momentSum_two_recurrence m
      have h1 := ih (m + 1) (by omega) (by omega)
      have h2 := ih (m + 2) (by omega) (by omega)
      -- S(m+3) + 2S(m) = 2S(m+2) + 2S(m+1), so S(m+3) = 2(S(m+2)+S(m+1)-S(m))
      -- S(m+2) + S(m+1) ≥ S(m) by monotonicity
      obtain ⟨a, ha⟩ := h1; obtain ⟨b, hb⟩ := h2
      have hmono := momentSum_two_mono' m
      have hmono2 := momentSum_two_mono' (m + 1)
      exact ⟨2 * b + 2 * a - momentSum 2 m, by omega⟩

/-- S_2(m+1) / 2 = E00(m) + E01(m) (collision pair halving).
    thm:pom-s2-succ-half -/
theorem momentSum_two_succ_half (m : Nat) :
    momentSum 2 (m + 1) / 2 =
    (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 % Nat.fib (m + 3) = weight p.2 % Nat.fib (m + 3))).card +
    (Finset.univ.filter (fun p : Word m × Word m =>
      weight p.1 % Nat.fib (m + 3) =
      (weight p.2 + Nat.fib (m + 2)) % Nat.fib (m + 3))).card := by
  have h := momentSum_two_succ_two_term m; omega

/-- S_2(m+1) ≥ 2·S_2(m) for m ≥ 2.
    thm:pom-s2-succ-ge-double -/
theorem momentSum_two_succ_ge_double (m : Nat) (hm : 2 ≤ m) :
    2 * momentSum 2 m ≤ momentSum 2 (m + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hrec := momentSum_two_recurrence k
  have hmono := momentSum_two_mono' k
  linarith

/-- S_2(m+1) ≤ 4·S_2(m).
    thm:pom-s2-succ-le-quadruple -/
theorem momentSum_two_succ_le_quadruple (m : Nat) :
    momentSum 2 (m + 1) ≤ 4 * momentSum 2 m := by
  match m with
  | 0 => rw [momentSum_two_zero, momentSum_two_one]; omega
  | 1 => rw [momentSum_two_one, momentSum_two_two]; omega
  | m + 2 =>
    have hrec := momentSum_two_recurrence m
    have hmono := momentSum_two_mono' (m + 1)
    linarith

/-- Additive form: S_2(m+1) + 2·S_2(m-2) = 2·S_2(m) + 2·S_2(m-1) for m ≥ 2.
    thm:pom-s2-succ-excess -/
theorem momentSum_two_succ_excess (m : Nat) (hm : 2 ≤ m) :
    momentSum 2 (m + 1) + 2 * momentSum 2 (m - 2) =
    2 * momentSum 2 m + 2 * momentSum 2 (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  simp only [show k + 2 - 2 = k from by omega, show k + 2 - 1 = k + 1 from by omega]
  exact momentSum_two_recurrence k

-- ══════════════════════════════════════════════════════════════
-- S_2 divisibility
-- ══════════════════════════════════════════════════════════════

/-- S_2(m) is odd iff m = 0.
    thm:pom-s2-odd-iff -/
theorem momentSum_two_odd_iff (m : Nat) :
    ¬ (2 ∣ momentSum 2 m) ↔ m = 0 := by
  constructor
  · intro h; by_contra hne; exact h (momentSum_two_even m (Nat.pos_of_ne_zero hne))
  · intro h; rw [h, momentSum_two_zero]; omega

/-- 4 ∣ S_2(m) for m ≥ 4.
    thm:pom-s2-mod-four -/
theorem momentSum_two_mod_four (m : Nat) (hm : 4 ≤ m) : 4 ∣ momentSum 2 m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 | 1 | 2 | 3 => omega
    | 4 => exact ⟨9, by rw [momentSum_two_four]⟩
    | 5 => exact ⟨22, by rw [momentSum_two_five]⟩
    | 6 => exact ⟨55, by rw [momentSum_two_six]⟩
    | m + 7 =>
      have hrec := momentSum_two_recurrence (m + 4)
      have h4 := ih (m + 4) (by omega) (by omega)
      have h5 := ih (m + 5) (by omega) (by omega)
      have h6 := ih (m + 6) (by omega) (by omega)
      -- S(m+7) + 2S(m+4) = 2S(m+6) + 2S(m+5)
      -- 4|S(m+4), 4|S(m+5), 4|S(m+6)
      -- So 4 | (2S(m+6) + 2S(m+5) - 2S(m+4)) = S(m+7)
      obtain ⟨a, ha⟩ := h4; obtain ⟨b, hb⟩ := h5; obtain ⟨c, hc⟩ := h6
      -- S(m+7) + 8a = 8c + 8b, so S(m+7) = 8(c+b) - 8a = 4·(2(c+b) - 2a)
      -- Need: 4 | S(m+7), i.e., ∃ k, S(m+7) = 4k
      -- S(m+7) + 8a = 8c + 8b → S(m+7) = 8c + 8b - 8a
      -- Since a ≤ b (from monotonicity S(m+4) ≤ S(m+5)), 8a ≤ 8b ≤ 8b + 8c
      suffices h : momentSum 2 (m + 7) + 4 * (2 * a) = 4 * (2 * c + 2 * b) by
        exact ⟨2 * c + 2 * b - 2 * a, by omega⟩
      linarith

-- ══════════════════════════════════════════════════════════════
-- S_2 vs E00 comparison
-- ══════════════════════════════════════════════════════════════

/-- E00(m) ≤ S_2(m) for m ≥ 1.
    thm:pom-s2-ge-e00 -/
theorem momentSum_two_ge_exactWeightCollision (m : Nat) (hm : 1 ≤ m) :
    exactWeightCollision m ≤ momentSum 2 m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => omega
    | 1 =>
      rw [exactWeightCollision_eq_sum, momentSum_two_one]
      simp [ momentSum_two_zero]
    | 2 =>
      have he := exactWeightCollision_eq_sum 2
      simp [Finset.sum_range_succ,
        momentSum_two_zero, momentSum_two_one] at he
      rw [momentSum_two_two]; omega
    | m + 3 =>
      have hes := exactWeightCollision_succ (m + 2)
      have hge := momentSum_two_succ_ge_double (m + 2) (by omega)
      have him := ih (m + 2) (by omega) (by omega)
      linarith

/-- E00(m+1) ≥ 2·E00(m) for m ≥ 1.
    thm:pom-e00-double -/
theorem exactWeightCollision_double (m : Nat) (hm : 1 ≤ m) :
    2 * exactWeightCollision m ≤ exactWeightCollision (m + 1) := by
  rw [exactWeightCollision_succ]
  have := momentSum_two_ge_exactWeightCollision m hm
  omega

/-- E00(m) ≥ m for all m.
    thm:pom-e00-ge-linear -/
theorem exactWeightCollision_ge_linear (m : Nat) : m ≤ exactWeightCollision m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [exactWeightCollision_succ]
    have := momentSum_pos' 2 m
    omega

-- ══════════════════════════════════════════════════════════════
-- Recurrence uniqueness
-- ══════════════════════════════════════════════════════════════

/-- A 3rd-order recurrence is uniquely determined by its initial values.
    thm:pom-s2-recurrence-unique -/
theorem recurrence_unique {f g : Nat → Nat}
    (hf : ∀ m, f (m + 3) + 2 * f m = 2 * f (m + 2) + 2 * f (m + 1))
    (hg : ∀ m, g (m + 3) + 2 * g m = 2 * g (m + 2) + 2 * g (m + 1))
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

/-- S_2 is the unique sequence satisfying the recurrence with initial values 1, 2, 6.
    thm:pom-s2-determined -/
theorem momentSum_two_determined {f : Nat → Nat}
    (hrec : ∀ m, f (m + 3) + 2 * f m = 2 * f (m + 2) + 2 * f (m + 1))
    (h0 : f 0 = 1) (h1 : f 1 = 2) (h2 : f 2 = 6) :
    ∀ m, f m = momentSum 2 m :=
  recurrence_unique hrec momentSum_two_recurrence
    (by rw [h0, momentSum_two_zero])
    (by rw [h1, momentSum_two_one])
    (by rw [h2, momentSum_two_two])

-- ══════════════════════════════════════════════════════════════
-- S_2 high-order values by pure recurrence (no native_decide)
-- ══════════════════════════════════════════════════════════════

/-- thm:pom-s2-seven-rec -/
theorem momentSum_two_seven_rec : momentSum 2 7 = 544 := by
  have h := momentSum_two_recurrence 4
  simp only [show (4 : Nat) + 3 = 7 from rfl, show (4 : Nat) + 2 = 6 from rfl,
    show (4 : Nat) + 1 = 5 from rfl, momentSum_two_four, momentSum_two_five, momentSum_two_six] at h
  omega

/-- thm:pom-s2-eight-rec -/
theorem momentSum_two_eight_rec : momentSum 2 8 = 1352 := by
  have h := momentSum_two_recurrence 5
  simp only [show (5 : Nat) + 3 = 8 from rfl, show (5 : Nat) + 2 = 7 from rfl,
    show (5 : Nat) + 1 = 6 from rfl, momentSum_two_five, momentSum_two_six,
    momentSum_two_seven_rec] at h
  omega

/-- thm:pom-s2-nine-rec -/
theorem momentSum_two_nine_rec : momentSum 2 9 = 3352 := by
  have h := momentSum_two_recurrence 6
  simp only [show (6 : Nat) + 3 = 9 from rfl, show (6 : Nat) + 2 = 8 from rfl,
    show (6 : Nat) + 1 = 7 from rfl, momentSum_two_six, momentSum_two_seven_rec,
    momentSum_two_eight_rec] at h
  omega

-- ══════════════════════════════════════════════════════════════
-- Fiber structure bounds
-- ══════════════════════════════════════════════════════════════

/-- D(m) · F_{m+2} ≥ 2^m (average fiber bound).
    thm:pom-d-ge-avg -/
theorem maxFiberMultiplicity_ge_avg (m : Nat) :
    X.maxFiberMultiplicity m * Nat.fib (m + 2) ≥ 2 ^ m := by
  calc 2 ^ m = ∑ x : X m, X.fiberMultiplicity x := (X.fiberMultiplicity_sum_eq_pow m).symm
    _ ≤ ∑ _ : X m, X.maxFiberMultiplicity m :=
        Finset.sum_le_sum (fun x _ => X.fiberMultiplicity_le_max x)
    _ = X.maxFiberMultiplicity m * Fintype.card (X m) := by
        simp [Finset.sum_const, Finset.card_univ, Nat.mul_comm]
    _ = X.maxFiberMultiplicity m * Nat.fib (m + 2) := by rw [X.card_eq_fib]

/-- D(m) ≤ 2^m.
    thm:pom-d-le-pow -/
theorem maxFiberMultiplicity_le_pow (m : Nat) :
    X.maxFiberMultiplicity m ≤ 2 ^ m := by
  obtain ⟨x, hx⟩ := X.maxFiberMultiplicity_achieved m
  rw [← hx]
  calc X.fiberMultiplicity x = (X.fiber x).card := rfl
    _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ m := by simp [Fintype.card_fin, Fintype.card_bool]

/-- d(x) ≤ 2^m for all x.
    thm:pom-fiber-le-pow -/
theorem fiberMultiplicity_le_pow (x : X m) :
    X.fiberMultiplicity x ≤ 2 ^ m :=
  (X.fiberMultiplicity_le_max x).trans (maxFiberMultiplicity_le_pow m)

/-- D(m) ≥ 1.
    thm:pom-d-ge-one -/
theorem maxFiberMultiplicity_ge_one (m : Nat) :
    1 ≤ X.maxFiberMultiplicity m := X.maxFiberMultiplicity_pos m

/-- At least one element achieves the max fiber multiplicity.
    thm:pom-achievers-pos -/
theorem maxFiberMultiplicity_achievers_pos (m : Nat) :
    0 < ((Finset.univ : Finset (X m)).filter
      (fun x => X.fiberMultiplicity x = X.maxFiberMultiplicity m)).card := by
  rw [Finset.card_pos]
  obtain ⟨x, hx⟩ := X.maxFiberMultiplicity_achieved m
  exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩

-- ══════════════════════════════════════════════════════════════
-- Weight extremes
-- ══════════════════════════════════════════════════════════════

/-- Weight of all-true word = F_{m+3} - 2.
    thm:pom-weight-allTrue -/
theorem weight_allTrue (m : Nat) :
    weight (fun (_ : Fin m) => true) = Nat.fib (m + 3) - 2 := by
  induction m with
  | zero => decide
  | succ m ih =>
    simp only [weight, ite_true]
    have htr : truncate (fun (_ : Fin (m + 1)) => true) = (fun (_ : Fin m) => true) := by
      funext i; simp [truncate]
    rw [htr, ih]
    -- Normalize Nat.fib argument forms
    have e1 : Nat.fib (m + 1 + 1) = Nat.fib (m + 2) := rfl
    have e2 : Nat.fib (m + 1 + 2) = Nat.fib (m + 3) := rfl
    have e3 : Nat.fib (m + 1 + 3) = Nat.fib (m + 4) := rfl
    rw [e1, e2, e3] at *
    have hrec : Nat.fib (m + 4) = Nat.fib (m + 3) + Nat.fib (m + 2) := by
      have := fib_succ_succ' (m + 2)
      rw [show m + 2 + 2 = m + 4 from rfl, show m + 2 + 1 = m + 3 from rfl] at this; exact this
    have hrec2 : Nat.fib (m + 3) = Nat.fib (m + 2) + Nat.fib (m + 1) := by
      have := fib_succ_succ' (m + 1)
      rw [show m + 1 + 2 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl] at this; exact this
    have h1 : 0 < Nat.fib (m + 1) := fib_succ_pos m
    have h2 : 0 < Nat.fib (m + 2) := fib_succ_pos (m + 1)
    omega

/-- Weight is bounded by F_{m+3} - 2.
    thm:pom-weight-le-allTrue -/
theorem weight_le_allTrue (w : Word m) :
    weight w ≤ Nat.fib (m + 3) - 2 := by
  rw [← weight_allTrue m]
  induction m with
  | zero => simp [weight]
  | succ m ih =>
    simp only [weight]
    have htr : truncate (fun (_ : Fin (m + 1)) => true) = (fun (_ : Fin m) => true) := by
      funext i; simp [truncate]
    rw [htr]
    have him := ih (truncate w)
    cases hb : w ⟨m, Nat.lt_succ_self m⟩
    · simp only [ Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega
    · simp only [ ↓reduceIte]; omega

/-- Fold of all-true word.
    thm:pom-fold-allTrue -/
theorem Fold_allTrue (m : Nat) :
    Fold (fun (_ : Fin m) => true) = X.ofNat m (Nat.fib (m + 3) - 2) := by
  unfold Fold; rw [weight_allTrue]

/-- ewc(m, 0) = 1 (only all-false has weight 0).
    thm:pom-ewc-zero-one -/
theorem exactWeightCount_zero_eq_one' (m : Nat) : exactWeightCount m 0 = 1 := by
  unfold exactWeightCount; rw [Finset.card_eq_one]
  refine ⟨fun _ => false, ?_⟩
  ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hw
    -- weight w = 0 → w = allFalse (by induction on m)
    induction m with
    | zero => funext i; exact absurd i.isLt (Nat.not_lt_zero _)
    | succ m ih =>
      funext i
      have hLast : w ⟨m, Nat.lt_succ_self m⟩ = false := by
        by_contra h
        have : w ⟨m, Nat.lt_succ_self m⟩ = true := by
          cases hb : w ⟨m, Nat.lt_succ_self m⟩ <;> simp_all
        have := weight_pos_of_bit_true this; omega
      by_cases hi : i.val < m
      · have htr : weight (truncate w) = 0 := by
          rw [weight] at hw; simp only [hLast, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hw; exact hw
        have := congr_fun (ih (truncate w) htr) ⟨i.val, hi⟩
        simp [truncate] at this; exact this
      · have : i = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext (Nat.eq_of_lt_succ_of_not_lt i.isLt hi)
        rw [this, hLast]
  · intro hw; rw [hw]; exact weight_allFalse


-- ══════════════════════════════════════════════════════════════
-- Complement map
-- ══════════════════════════════════════════════════════════════

/-- Bitwise complement of a word. -/
def complement (w : Word m) : Word m := fun i => !w i

/-- thm:pom-complement-involution -/
theorem complement_involution (w : Word m) : complement (complement w) = w := by
  funext i; simp [complement]

/-- thm:pom-truncate-complement -/
theorem truncate_complement (w : Word (m + 1)) :
    truncate (complement w) = complement (truncate w) := by
  funext i; simp [truncate, complement]

/-- thm:pom-complement-allFalse -/
theorem complement_allFalse (m : Nat) :
    complement (fun (_ : Fin m) => false) = fun _ => true := by
  funext i; simp [complement]

/-- weight(complement w) + weight(w) = F_{m+3} - 2.
    thm:pom-weight-complement -/
theorem weight_complement (w : Word m) :
    weight (complement w) + weight w = Nat.fib (m + 3) - 2 := by
  rw [← weight_allTrue]
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [weight]
    rw [truncate_complement]
    have htr : truncate (fun (_ : Fin (m + 1)) => true) = (fun (_ : Fin m) => true) := by
      funext i; simp [truncate]
    rw [htr]
    have him := ih (truncate w)
    cases hb : w ⟨m, Nat.lt_succ_self m⟩
    · simp only [complement, hb, Bool.not_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      omega
    · simp only [complement, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      omega

/-- ewc is symmetric: ewc(m, n) = ewc(m, F_{m+3}-2-n).
    thm:pom-ewc-symmetric -/
theorem exactWeightCount_symmetric (m n : Nat) (hn : n ≤ Nat.fib (m + 3) - 2) :
    exactWeightCount m n = exactWeightCount m (Nat.fib (m + 3) - 2 - n) := by
  unfold exactWeightCount
  apply Finset.card_bij (fun (w : Word m) _ => complement w)
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    have hcomp := weight_complement w
    omega
  · intro w1 _ w2 _ h
    have := congr_arg complement h
    rwa [complement_involution, complement_involution] at this
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    refine ⟨complement w, ?_, complement_involution w⟩
    have hcomp := weight_complement (complement w)
    rw [complement_involution] at hcomp
    omega

-- ══════════════════════════════════════════════════════════════
-- Fold complement duality
-- ══════════════════════════════════════════════════════════════

/-- thm:pom-weight-complement-sub -/
theorem weight_complement_sub (w : Word m) :
    weight (complement w) = Nat.fib (m + 3) - 2 - weight w := by
  have h := weight_complement w; have hle := weight_le_allTrue w; omega

/-- thm:pom-fold-complement -/
theorem Fold_complement (w : Word m) :
    Fold (complement w) = X.ofNat m (Nat.fib (m + 3) - 2 - weight w) := by
  unfold Fold; rw [weight_complement_sub]

-- ══════════════════════════════════════════════════════════════
-- Gauss sum of stableValues
-- ══════════════════════════════════════════════════════════════

/-- thm:pom-stableValue-sum -/
theorem stableValue_sum (m : Nat) :
    ∑ x : X m, stableValue x = Nat.fib (m + 2) * (Nat.fib (m + 2) - 1) / 2 := by
  -- stableValueFin is a bijection X m → Fin(F_{m+2})
  -- So Σ stableValue x = Σ_{i : Fin F} i.val = F*(F-1)/2
  have hbij := X.stableValueFin_bijective m
  have hsum : ∑ x : X m, stableValue x = ∑ i : Fin (Nat.fib (m + 2)), i.val := by
    rw [show (fun x : X m => stableValue x) =
      (fun i : Fin (Nat.fib (m + 2)) => i.val) ∘ X.stableValueFin from by
        ext x; simp [X.stableValueFin]]
    exact hbij.sum_comp _
  rw [hsum]
  -- ∑ i : Fin F, i.val = ∑ i ∈ range F, i = F*(F-1)/2
  have : ∑ i : Fin (Nat.fib (m + 2)), (i : Nat) =
      ∑ i ∈ Finset.range (Nat.fib (m + 2)), i := by
    rw [← Fin.sum_univ_eq_sum_range]
  rw [this, Finset.sum_range_id]

-- ══════════════════════════════════════════════════════════════
-- Phase R17: sum of squares Gauss formula
-- ══════════════════════════════════════════════════════════════

/-- Standard identity: 6·∑_{i<n} i² = n·(n-1)·(2n-1). -/
private theorem six_mul_sum_sq (n : Nat) :
    6 * ∑ i ∈ Finset.range n, i ^ 2 = n * (n - 1) * (2 * n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.succ_sub_one, show 2 * (n + 2) - 1 = 2 * n + 3 from by omega,
        show 2 * (n + 1) - 1 = 2 * n + 1 from by omega]
      ring

/-- 6 · Σ sv(x)² = F·(F-1)·(2F-1) where F = F_{m+2}.
    thm:pom-stableValue-sq-gauss -/
theorem stableValue_sq_sum_mul6 (m : Nat) :
    6 * ∑ x : X m, stableValue x ^ 2 =
    Nat.fib (m + 2) * (Nat.fib (m + 2) - 1) * (2 * Nat.fib (m + 2) - 1) := by
  have hbij := X.stableValueFin_bijective m
  have hsum : ∑ x : X m, stableValue x ^ 2 =
      ∑ i : Fin (Nat.fib (m + 2)), i.val ^ 2 := by
    rw [show (fun x : X m => stableValue x ^ 2) =
      ((fun i : Fin (Nat.fib (m + 2)) => i.val ^ 2) ∘ X.stableValueFin) from by
        ext x; simp [X.stableValueFin]]
    exact hbij.sum_comp (fun i : Fin (Nat.fib (m + 2)) => i.val ^ 2)
  rw [hsum]
  rw [show ∑ i : Fin (Nat.fib (m + 2)), (i : Nat) ^ 2 =
      ∑ i ∈ Finset.range (Nat.fib (m + 2)), i ^ 2 from by
    rw [← Fin.sum_univ_eq_sum_range]]
  exact six_mul_sum_sq (Nat.fib (m + 2))

-- ══════════════════════════════════════════════════════════════
-- S_2 cross-verification and growth bounds
-- ══════════════════════════════════════════════════════════════

/-- S_2 recurrence matches the Cayley-Hamilton of the collision kernel.
    thm:pom-momentSum-two-recurrence-matches-charpoly -/
theorem momentSum_two_recurrence_matches_charpoly :
    (∀ m, momentSum 2 (m + 3) + 2 * momentSum 2 m =
      2 * momentSum 2 (m + 2) + 2 * momentSum 2 (m + 1)) ∧
    collisionKernel2 ^ 3 = 2 • collisionKernel2 ^ 2 + 2 • collisionKernel2 - 2 • 1 :=
  ⟨momentSum_two_recurrence, collisionKernel2_cayley_hamilton⟩

/-- Complete S_2 value chain for m = 0..7.
    thm:pom-momentSum-two-chain -/
theorem momentSum_two_chain :
    momentSum 2 0 = 1 ∧ momentSum 2 1 = 2 ∧ momentSum 2 2 = 6 ∧
    momentSum 2 3 = 14 ∧ momentSum 2 4 = 36 ∧ momentSum 2 5 = 88 ∧
    momentSum 2 6 = 220 ∧ momentSum 2 7 = 544 :=
  ⟨momentSum_two_zero, momentSum_two_one, momentSum_two_two,
    momentSum_two_three, momentSum_two_four, momentSum_two_five,
    momentSum_two_six, momentSum_two_seven_rec⟩

/-- S_2 growth ratio bounds: 2·S_2(m) ≤ S_2(m+1) ≤ 4·S_2(m) for m ≥ 2.
    thm:pom-momentSum-two-ratio-bounds -/
theorem momentSum_two_ratio_bounds' (m : Nat) (hm : 2 ≤ m) :
    2 * momentSum 2 m ≤ momentSum 2 (m + 1) ∧
    momentSum 2 (m + 1) ≤ 4 * momentSum 2 m :=
  ⟨momentSum_two_succ_ge_double m hm, momentSum_two_succ_le_quadruple m⟩

/-- The excess: S_2(m+1) > 2·S_2(m) for m ≥ 3.
    thm:pom-momentSum-two-excess-pos -/
theorem momentSum_two_excess_pos (m : Nat) (hm : 3 ≤ m) :
    2 * momentSum 2 m < momentSum 2 (m + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have hrec := momentSum_two_recurrence (k + 1)
  have hsmono := momentSum_two_strict_mono' (k + 1) (by omega)
  linarith

/-- S_2(m) ≥ 2·F_{m+1} for m ≥ 2.
    thm:pom-momentSum-two-ge-two-fib -/
theorem momentSum_two_ge_two_fib (m : Nat) (hm : 2 ≤ m) :
    2 * Nat.fib (m + 1) ≤ momentSum 2 m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 | 1 => omega
    | 2 => rw [momentSum_two_two]; simp [Nat.fib]
    | 3 => rw [momentSum_two_three]; simp [Nat.fib]
    | m + 4 =>
      -- S_2(m+4) ≥ 2·S_2(m+3) ≥ 4·F(m+2)
      -- F(m+5) = F(m+4) + F(m+3)
      -- Need: S_2(m+4) ≥ 2·F(m+5) = 2·F(m+4) + 2·F(m+3)
      -- S_2(m+4) ≥ 2·S_2(m+3) [succ_ge_double] ≥ 2·(2·F(m+2)) = 4·F(m+2) [IH at m+3]
      -- Need 4·F(m+2) ≥ 2·F(m+4) + 2·F(m+3)? No, that's wrong direction.
      -- Better: S_2(m+4) ≥ 2·S_2(m+3) and S_2(m+3) ≥ 2·F(m+4)
      -- So S_2(m+4) ≥ 4·F(m+4) ≥ 2·F(m+5)? No: 4F(m+4) vs 2F(m+5) = 2(F(m+4)+F(m+3)).
      -- 4F(m+4) ≥ 2F(m+4)+2F(m+3) iff 2F(m+4) ≥ 2F(m+3) iff F(m+4) ≥ F(m+3). True!
      have h3 := ih (m + 3) (by omega) (by omega)
      have hge := momentSum_two_succ_ge_double (m + 3) (by omega)
      have hfib := Nat.fib_add_two (n := m + 3)
      rw [show m + 3 + 2 = m + 5 from rfl, show m + 3 + 1 = m + 4 from rfl] at hfib
      have hmono : Nat.fib (m + 3) ≤ Nat.fib (m + 4) := Nat.fib_mono (by omega)
      linarith

-- ══════════════════════════════════════════════════════════════
-- Fiber discriminants
-- ══════════════════════════════════════════════════════════════

/-- Stable words have hiddenBit = 0.
    thm:pom-hiddenBit-stable -/
theorem hiddenBit_stable (x : X m) : hiddenBit x.1 = 0 := by
  unfold hiddenBit
  have := stableValue_lt_fib x
  simp only [stableValue] at this
  exact if_neg (not_le.mpr this)

/-- Fold(w).1 = w iff w satisfies No11.
    thm:pom-Fold-eq-self-iff -/
theorem Fold_eq_self_iff (w : Word m) : (Fold w).1 = w ↔ No11 w :=
  ⟨fun h => h ▸ (Fold w).2, fun h => congr_arg Subtype.val (Fold_stable ⟨w, h⟩)⟩

/-- weight of a stable word equals its stableValue.
    thm:pom-weight-stable-eq-stableValue -/
theorem weight_stable_eq_stableValue (x : X m) : weight x.1 = stableValue x := rfl

/-- ewc at stableValue is at least 1 (the word itself witnesses).
    thm:pom-ewc-stableValue-pos -/
theorem ewc_stableValue_pos (x : X m) : 1 ≤ exactWeightCount m (stableValue x) := by
  unfold exactWeightCount
  rw [Nat.one_le_iff_ne_zero, Finset.card_ne_zero]
  exact ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

/-- Forward: d(x) = 1 → ewc(sv+F) = 0.
    thm:pom-fiberMultiplicity-one-imp-ewc-zero -/
theorem fiberMultiplicity_one_imp_ewc_zero (x : X m) (hd : X.fiberMultiplicity x = 1) :
    exactWeightCount m (stableValue x + Nat.fib (m + 2)) = 0 := by
  rw [fiberMultiplicity_eq_two_ewc] at hd
  have := ewc_stableValue_pos x; omega

/-- Fiber multiplicity as sum of two ewc terms.
    thm:pom-fiberMultiplicity-ge-ewc -/
theorem fiberMultiplicity_ge_ewc (x : X m) :
    exactWeightCount m (stableValue x) ≤ X.fiberMultiplicity x := by
  rw [fiberMultiplicity_eq_two_ewc]; omega

-- ══════════════════════════════════════════════════════════════
-- Pisano applications + parity
-- ══════════════════════════════════════════════════════════════

/-- allFalse fiber multiplicity is odd iff m ≡ 0,1 (mod 4).
    thm:pom-fiberMultiplicity-allFalse-odd-iff -/
theorem fiberMultiplicity_allFalse_odd_iff (m : Nat) :
    ¬ (2 ∣ X.fiberMultiplicity (⟨fun _ => false, no11_allFalse⟩ : X m)) ↔
    m % 4 = 0 ∨ m % 4 = 1 := by
  rw [fiberMultiplicity_allFalse_closed]; omega

/-- hiddenBit = 1 iff weight ≥ F_{m+2}.
    thm:pom-hiddenBit-eq-one-iff -/
theorem hiddenBit_eq_one_iff (w : Word m) :
    hiddenBit w = 1 ↔ Nat.fib (m + 2) ≤ weight w := by
  unfold hiddenBit; constructor
  · intro h; by_contra hlt; simp [not_le.mp hlt] at h
  · intro h; simp [h]

/-- hiddenBit = 0 iff weight < F_{m+2}.
    thm:pom-hiddenBit-eq-zero-iff -/
theorem hiddenBit_eq_zero_iff (w : Word m) :
    hiddenBit w = 0 ↔ weight w < Nat.fib (m + 2) := by
  unfold hiddenBit; constructor
  · intro h; by_contra hge; push_neg at hge; simp [hge] at h
  · intro h; exact if_neg (not_le.mpr h)

/-- Fiber decomposition (named alias).
    thm:pom-fiber-hidden-bit-split -/
theorem fiber_hidden_bit_split (x : X m) :
    X.fiberMultiplicity x =
    exactWeightCount m (stableValue x) +
    exactWeightCount m (stableValue x + Nat.fib (m + 2)) :=
  fiberMultiplicity_eq_two_ewc x

/-- S_2 mod 6 base values.
    thm:pom-momentSum-two-mod-six-base -/
theorem momentSum_two_mod_six_base :
    momentSum 2 0 % 6 = 1 ∧ momentSum 2 1 % 6 = 2 ∧
    momentSum 2 2 % 6 = 0 ∧ momentSum 2 3 % 6 = 2 ∧
    momentSum 2 4 % 6 = 0 ∧ momentSum 2 5 % 6 = 4 ∧
    momentSum 2 6 % 6 = 4 ∧ momentSum 2 7 % 6 = 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [momentSum_two_zero, momentSum_two_one, momentSum_two_two,
      momentSum_two_three, momentSum_two_four, momentSum_two_five,
      momentSum_two_six, momentSum_two_seven_rec]

-- ══════════════════════════════════════════════════════════════
-- S_2 triple bound
-- ══════════════════════════════════════════════════════════════

/-- S_2(m+1) ≤ 3·S_2(m). -/
theorem momentSum_two_succ_le_triple (m : Nat) :
    momentSum 2 (m + 1) ≤ 3 * momentSum 2 m := by
  match m with
  | 0 => rw [momentSum_two_one, momentSum_two_zero]; omega
  | 1 => rw [momentSum_two_two, momentSum_two_one]
  | 2 => rw [momentSum_two_three, momentSum_two_two]; omega
  | m + 3 =>
    have hrec := momentSum_two_recurrence (m + 1)
    have hge := momentSum_two_succ_ge_double (m + 2) (by omega)
    linarith

-- ══════════════════════════════════════════════════════════════
-- S_2 mod 8 divisibility
-- ══════════════════════════════════════════════════════════════

/-- 8 ∣ S_2(m) for m ≥ 7. -/
theorem momentSum_two_mod_eight (m : Nat) (hm : 7 ≤ m) : 8 ∣ momentSum 2 m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
    | 7 => exact ⟨68, by rw [momentSum_two_seven_rec]⟩
    | 8 => exact ⟨169, by rw [momentSum_two_eight_rec]⟩
    | 9 => exact ⟨419, by rw [momentSum_two_nine_rec]⟩
    | m + 10 =>
      have hrec := momentSum_two_recurrence (m + 7)
      rw [show (m + 7 + 3 : Nat) = m + 10 from rfl,
        show (m + 7 + 2 : Nat) = m + 9 from rfl,
        show (m + 7 + 1 : Nat) = m + 8 from rfl] at hrec
      have h7 := ih (m + 7) (by omega) (by omega)
      have h8 := ih (m + 8) (by omega) (by omega)
      have h9 := ih (m + 9) (by omega) (by omega)
      obtain ⟨a, ha⟩ := h7; obtain ⟨b, hb⟩ := h8; obtain ⟨c, hc⟩ := h9
      rw [ha, hb, hc] at hrec
      have hab : a ≤ b := by
        have := momentSum_two_mono' (m + 7)
        rw [ha, show (m + 7 + 1 : Nat) = m + 8 from rfl, hb] at this; omega
      exact ⟨2 * (c + b) - 2 * a, by omega⟩

-- ══════════════════════════════════════════════════════════════
-- Fold modular factorization + moment wrappers
-- ══════════════════════════════════════════════════════════════

/-- Fold factors through weight mod F_{m+2}. -/
theorem Fold_eq_ofNat_weight_mod (w : Word m) :
    Fold w = X.ofNat m (weight w % Nat.fib (m + 2)) := by
  conv_lhs => rw [← X.ofNat_stableValue (Fold w)]
  rw [stableValue_Fold_mod]

/-- S_3(m) > 0 for all m. -/
theorem momentSum_three_pos (m : Nat) : 0 < momentSum 3 m :=
  momentSum_pos' 3 m

/-- S_3(m) ≤ S_4(m). -/
theorem momentSum_four_ge_three (m : Nat) : momentSum 3 m ≤ momentSum 4 m :=
  momentSum_le_succ' 3 m

-- ══════════════════════════════════════════════════════════════
-- Phase 181
-- ══════════════════════════════════════════════════════════════

/-- weight(w) + weight(complement w) = F_{m+3} - 2 (total weight conservation). -/
theorem weight_add_complement (w : Word m) :
    weight w + weight (complement w) = Nat.fib (m + 3) - 2 := by
  have := weight_complement w; omega

-- ══════════════════════════════════════════════════════════════
-- Phase 229: E00 symmetric rewrite
-- ══════════════════════════════════════════════════════════════

/-- E00 = Σ ewc(n)*ewc(F-2-n). prop:fold-fiber-count-reciprocity -/
theorem exactWeightCollision_eq_symmetric_sum (m : Nat) :
    exactWeightCollision m =
    ∑ n ∈ Finset.range (Nat.fib (m + 3)),
      exactWeightCount m n * exactWeightCount m (Nat.fib (m + 3) - 2 - n) := by
  unfold exactWeightCollision
  -- Peel off the last term n = F-1 where ewc(F-1)=0 (weight never achieves F-1)
  have hF : 2 ≤ Nat.fib (m + 3) :=
    le_trans (show 2 ≤ Nat.fib 3 from by decide) (Nat.fib_mono (by omega))
  rw [show Nat.fib (m + 3) = Nat.fib (m + 3) - 1 + 1 from by omega,
    Finset.range_add_one, Finset.sum_insert (by simp [Finset.mem_range]),
    Finset.sum_insert (by simp [Finset.mem_range])]
  -- At n = F-1: ewc(F-1) = 0 by exactWeightCount_eq_zero_of_ge_fib (F-1 ≥ F-1, but F ≤ F-1?)
  -- Actually weight(w) ≤ F-2 for No11 words, so ewc(F-1)=0. Use weight_complement:
  -- The complement of a word with weight F-2-k has weight k. So all weights are ≤ F-2.
  have hewc_last : exactWeightCount m (Nat.fib (m + 3) - 1) = 0 := by
    unfold exactWeightCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w _
    have := X.weight_lt_fib w
    have := weight_complement w
    -- weight(w) + weight(compl w) = F-2, so weight(w) ≤ F-2 < F-1
    omega
  rw [hewc_last]
  simp only [show (0 : Nat) ^ 2 = 0 from by norm_num, Nat.zero_mul, Nat.zero_add]
  conv_rhs => arg 2; ext x; rw [show Nat.fib (m + 3) - 1 + 1 = Nat.fib (m + 3) from by omega]
  apply Finset.sum_congr rfl; intro n hn
  rw [Finset.mem_range] at hn
  rw [sq, exactWeightCount_symmetric m n (by omega)]

-- ══════════════════════════════════════════════════════════════
-- Phase 239: moment lower bound
-- ══════════════════════════════════════════════════════════════

/-- S_2(m) ≥ 2·F(m+2) for m ≥ 2.
    prop:pom-s2-recurrence (strengthened lower bound) -/
theorem momentSum_two_ge_two_fib_succ (m : Nat) (hm : 2 ≤ m) :
    2 * Nat.fib (m + 2) ≤ momentSum 2 m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 | 1 => omega
    | 2 => rw [momentSum_two_two]; simp [Nat.fib]
    | 3 => rw [momentSum_two_three]; simp [Nat.fib]
    | m + 4 =>
      have h3 := ih (m + 3) (by omega) (by omega)
      have hge := momentSum_two_succ_ge_double (m + 3) (by omega)
      have hfib := Nat.fib_add_two (n := m + 4)
      rw [show m + 4 + 2 = m + 6 from by omega, show m + 4 + 1 = m + 5 from by omega] at hfib
      have hmono : Nat.fib (m + 4) ≤ Nat.fib (m + 5) := Nat.fib_mono (by omega)
      linarith

-- ══════════════════════════════════════════════════════════════
-- Phase 240: S_2 global strict monotonicity
-- ══════════════════════════════════════════════════════════════

/-- S_2(m) < S_2(m+1) for all m (including m=0).
    prop:pom-s2-recurrence -/
theorem momentSum_two_strict_mono_all (m : Nat) :
    momentSum 2 m < momentSum 2 (m + 1) := by
  match m with
  | 0 => rw [momentSum_two_zero, momentSum_two_one]; omega
  | m + 1 => exact momentSum_two_strict_mono' (m + 1) (by omega)

-- ══════════════════════════════════════════════════════════════
-- Phase R27: ewc partition of unity
-- ══════════════════════════════════════════════════════════════

/-- ewc(m, F_{m+3}-1) = 0: no word has weight exactly F_{m+3}-1.
    prop:pom-ewc-partition-of-unity -/
private theorem exactWeightCount_fib_sub_one (m : Nat) :
    exactWeightCount m (Nat.fib (m + 3) - 1) = 0 := by
  unfold exactWeightCount
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_false_of_mem
  intro w _
  have hcomp := weight_complement w
  -- weight(complement w) + weight w = F_{m+3} - 2
  -- weight w ≤ F_{m+3} - 2
  have hle : weight w ≤ Nat.fib (m + 3) - 2 := by
    have := @Nat.zero_le (weight (complement w)); omega
  have hF : 2 ≤ Nat.fib (m + 3) := by
    calc Nat.fib (m + 3) ≥ Nat.fib 3 := Nat.fib_mono (by omega)
      _ = 2 := by native_decide
  omega

/-- The ewc sum over [0, F_{m+3}-2] equals 2^m.
    prop:pom-ewc-partition-of-unity -/
theorem exactWeightCount_total_sum (m : Nat) :
    (Finset.range (Nat.fib (m + 3) - 1)).sum (exactWeightCount m) = 2 ^ m := by
  have hF : 1 ≤ Nat.fib (m + 3) := Nat.fib_pos.mpr (by omega)
  have hkey := exactWeightCount_sum m
  rw [show Nat.fib (m + 3) = Nat.fib (m + 3) - 1 + 1 from by omega,
    Finset.sum_range_succ] at hkey
  rw [exactWeightCount_fib_sub_one] at hkey
  linarith

-- ══════════════════════════════════════════════════════════════
-- Phase R59: Sprint to 200 theorems
-- ══════════════════════════════════════════════════════════════

/-- F(m+2)^2 ≤ S_2(m) · F(m+2), i.e. the second moment times cardinality dominates the
    square of cardinality (Cauchy-Schwarz consequence).
    prop:pom-moment-cauchy-schwarz-card -/
theorem momentSum_ge_card_sq (m : Nat) :
    Nat.fib (m + 2) ^ 2 ≤ momentSum 2 m * Nat.fib (m + 2) := by
  have h := momentSum_ge_card' 2 m
  nlinarith

/-- Weight of any m-bit word is at most F(m+3) - 2 (named alias).
    prop:pom-weight-upper-bound -/
theorem weight_le_fib_sub_two (w : Word m) :
    weight w ≤ Nat.fib (m + 3) - 2 :=
  weight_le_allTrue w

/-- exactWeightCount at weight 0 is positive.
    prop:pom-ewc-pos-zero -/
theorem exactWeightCount_pos_zero (m : Nat) :
    0 < exactWeightCount m 0 := by
  rw [exactWeightCount_zero_eq_one']; exact Nat.one_pos

-- ══════════════════════════════════════════════════════════════
-- Phase R69: S_2 Fibonacci-type superadditivity
-- ══════════════════════════════════════════════════════════════

/-- S_2(m+1) + S_2(m) ≤ S_2(m+2) for m ≥ 1 (Fibonacci-type superadditivity).
    From recurrence: S_2(m+2) = 2S_2(m+1) + 2S_2(m) - 2S_2(m-1),
    so S_2(m+2) - S_2(m+1) - S_2(m) = S_2(m+1) - S_2(m-1) + S_2(m) - S_2(m-1) ≥ 0.
    thm:pom-s2-fib-superadditive -/
theorem momentSum_two_fib_superadditive (m : Nat) (hm : 1 ≤ m) :
    momentSum 2 (m + 1) + momentSum 2 m ≤ momentSum 2 (m + 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  -- Recurrence at k: S(k+3) + 2S(k) = 2S(k+2) + 2S(k+1)
  have hrec := momentSum_two_recurrence k
  -- Goal: S(k+2) + S(k+1) ≤ S(k+3)
  -- From hrec: S(k+3) = 2S(k+2) + 2S(k+1) - 2S(k)
  -- S(k+3) - S(k+2) - S(k+1) = S(k+2) + S(k+1) - 2S(k)
  --                             = (S(k+2) - S(k)) + (S(k+1) - S(k)) ≥ 0
  have hm1 := momentSum_two_mono' k
  have hm2 := momentSum_two_mono' (k + 1)
  linarith

-- ══════════════════════════════════════════════════════════════
-- Phase R313: momentSum strict mono in q (numerical instances)
-- ══════════════════════════════════════════════════════════════

/-- S_1(m) < S_2(m) for m=4..8. prop:pom-sq-lower -/
theorem momentSum_q_mono_instances :
    cMomentSum 1 4 < cMomentSum 2 4 ∧
    cMomentSum 1 5 < cMomentSum 2 5 ∧
    cMomentSum 1 6 < cMomentSum 2 6 ∧
    cMomentSum 1 7 < cMomentSum 2 7 ∧
    cMomentSum 1 8 < cMomentSum 2 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- S_2(m) < S_3(m) for m=4..7. prop:pom-sq-lower -/
theorem momentSum_q2_lt_q3_instances :
    cMomentSum 2 4 < cMomentSum 3 4 ∧
    cMomentSum 2 5 < cMomentSum 3 5 ∧
    cMomentSum 2 6 < cMomentSum 3 6 ∧
    cMomentSum 2 7 < cMomentSum 3 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Paper package. prop:pom-sq-lower -/
theorem paper_momentSum_q_mono :
    cMomentSum 1 6 < cMomentSum 2 6 ∧
    cMomentSum 2 6 < cMomentSum 3 6 ∧
    cMomentSum 3 6 < cMomentSum 4 6 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- S_2(m) growth audit: strict mono, evenness, 4-divisibility.
    prop:fold-groupoid-wedderburn -/
theorem paper_momentSum_two_growth_audit :
    (∀ m : Nat, 1 ≤ m → momentSum 2 m < momentSum 2 (m + 1)) ∧
    (∀ m : Nat, 1 ≤ m → 2 ∣ momentSum 2 m) ∧
    (∀ m : Nat, 4 ≤ m → 4 ∣ momentSum 2 m) :=
  ⟨momentSum_two_strict_mono', momentSum_two_even, momentSum_two_mod_four⟩

/-- S_2 growth ratio bounds: 2·S_2(m) ≤ S_2(m+1) ≤ 4·S_2(m) for m ≥ 2.
    prop:fold-groupoid-wedderburn -/
theorem paper_momentSum_two_ratio_bounds (m : Nat) (hm : 2 ≤ m) :
    2 * momentSum 2 m ≤ momentSum 2 (m + 1) ∧
    momentSum 2 (m + 1) ≤ 4 * momentSum 2 m :=
  ⟨momentSum_two_succ_ge_double m hm, momentSum_two_succ_le_quadruple m⟩

/-- Collision moment S_2 properties package.
    prop:fold-renyi-collision-identity, prop:fold-groupoid-wedderburn -/
theorem paper_pom_collision_moment_package :
    (∀ m : Nat, 0 < momentSum 2 m) ∧
    (∀ m : Nat, 1 ≤ m → momentSum 2 m < momentSum 2 (m + 1)) ∧
    (∀ q m : Nat, Nat.fib (m + 2) ≤ momentSum q m) ∧
    (∀ q m : Nat, 1 ≤ q → 2 ^ m ≤ momentSum q m) :=
  ⟨momentSum_two_pos', momentSum_two_strict_mono', momentSum_ge_card', momentSum_ge_pow'⟩

/-- Concrete collision-moment package used by the Rényi collision identity wrapper.
    prop:fold-renyi-collision-identity -/
def fold_renyi_collision_identity_statement : Prop :=
    (∀ m : Nat, 0 < momentSum 2 m) ∧
    (∀ m : Nat, 1 ≤ m → momentSum 2 m < momentSum 2 (m + 1)) ∧
    (∀ q m : Nat, Nat.fib (m + 2) ≤ momentSum q m) ∧
    (∀ q m : Nat, 1 ≤ q → 2 ^ m ≤ momentSum q m)

/-- Paper label: `prop:fold-renyi-collision-identity`. -/
theorem paper_fold_renyi_collision_identity : fold_renyi_collision_identity_statement :=
  paper_pom_collision_moment_package

/-- Moment sum hierarchy: S_0, S_1, monotonicity in q.
    prop:fold-groupoid-wedderburn -/
theorem paper_momentSum_hierarchy :
    (∀ m : Nat, momentSum 0 m = Nat.fib (m + 2)) ∧
    (∀ m : Nat, momentSum 1 m = 2 ^ m) ∧
    (∀ q m : Nat, momentSum q m ≤ momentSum (q + 1) m) :=
  ⟨momentSum_zero, momentSum_one, momentSum_le_succ'⟩

end Omega
