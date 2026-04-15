/-
Copyright (c) 2026 The Omega Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Fibonacci fusion identity and strict submultiplicativity.

Paper reference: lem:pom-fib-fusion-submultiplicativity, cor:pom-fib-component-fusion-gain
-/
import Omega.Core.Fib

namespace Omega

/-! ## Fibonacci fusion identity

The fusion identity `F(a+b-1) = F(a)*F(b) + F(a-1)*F(b-1)` is derived from
mathlib's `Nat.fib_add` by an index shift. -/

/-- Paper's fusion identity: F(a+b-1) = F(a)*F(b) + F(a-1)*F(b-1) for a, b >= 1.
    Derived from mathlib's Nat.fib_add by index shift.
    lem:pom-fib-fusion-submultiplicativity -/
theorem fib_fusion (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.fib (a + b - 1) = Nat.fib a * Nat.fib b + Nat.fib (a - 1) * Nat.fib (b - 1) := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hb
  -- Now a = 1 + a', b = 1 + b'
  -- Goal involves (1 + a'), (1 + b')
  have hsub1 : 1 + a' + (1 + b') - 1 = a' + b' + 1 := by omega
  have hsub2 : 1 + a' - 1 = a' := by omega
  have hsub3 : 1 + b' - 1 = b' := by omega
  rw [hsub1, hsub2, hsub3, Nat.fib_add a' b']
  ring_nf

/-- Strict submultiplicativity: F(a)*F(b) < F(a+b-1) when a >= 2 and b >= 2.
    lem:pom-fib-fusion-submultiplicativity-prod-lt-fusion -/
theorem fib_prod_lt_fib_fusion (a b : Nat) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    Nat.fib a * Nat.fib b < Nat.fib (a + b - 1) := by
  rw [fib_fusion a b (by omega) (by omega)]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos (Nat.fib_pos.mpr (by omega))
    (Nat.fib_pos.mpr (by omega)))

/-- F(a+b-1) < F(a+b) when a+b >= 3.
    lem:pom-fib-fusion-submultiplicativity-fusion-lt-sum -/
theorem fib_fusion_lt_fib_sum (a b : Nat) (_ha : 1 ≤ a) (_hb : 1 ≤ b)
    (hab : 3 ≤ a + b) :
    Nat.fib (a + b - 1) < Nat.fib (a + b) := by
  have hab2 : 2 ≤ a + b - 1 := by omega
  have hindex : a + b = (a + b - 1) + 1 := by omega
  rw [hindex]
  exact Nat.fib_lt_fib_succ hab2

/-- Combined: F(a)*F(b) < F(a+b) for a >= 2, b >= 2.
    lem:pom-fib-fusion-submultiplicativity-prod-lt-sum -/
theorem fib_prod_lt_fib_sum (a b : Nat) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    Nat.fib a * Nat.fib b < Nat.fib (a + b) :=
  Nat.lt_trans (fib_prod_lt_fib_fusion a b ha hb)
    (fib_fusion_lt_fib_sum a b (by omega) (by omega) (by omega))

/-! ## Component fusion gain

The component fusion gain theorem shows that merging two Fibonacci-indexed
components yields a strictly larger Fibonacci number, with a quantified gain. -/

/-- Component fusion gain: F(l+2)*F(l'+2) < F(l+l'+3) for l, l' >= 1.
    cor:pom-fib-component-fusion-gain -/
theorem fib_component_fusion_lt (l l' : Nat) (_hl : 1 ≤ l) (_hl' : 1 ≤ l') :
    Nat.fib (l + 2) * Nat.fib (l' + 2) < Nat.fib (l + l' + 3) := by
  have h : l + l' + 3 = (l + 2) + (l' + 2) - 1 := by omega
  rw [h]
  exact fib_prod_lt_fib_fusion (l + 2) (l' + 2) (by omega) (by omega)

/-- The fusion gain equals F(l+1)*F(l'+1).
    cor:pom-fib-component-fusion-gain-bound -/
theorem fib_component_fusion_gain (l l' : Nat) (_hl : 1 ≤ l) (_hl' : 1 ≤ l') :
    Nat.fib (l + l' + 3) - Nat.fib (l + 2) * Nat.fib (l' + 2) =
      Nat.fib (l + 1) * Nat.fib (l' + 1) := by
  have hfuse := fib_fusion (l + 2) (l' + 2) (by omega) (by omega)
  simp only [show l + 2 - 1 = l + 1 from by omega,
             show l' + 2 - 1 = l' + 1 from by omega] at hfuse
  have h : l + l' + 3 = (l + 2) + (l' + 2) - 1 := by omega
  rw [h, hfuse]
  omega

/-- The fusion gain is at least F(min(l, l') + 1).
    cor:pom-fib-component-fusion-gain-lower -/
theorem fib_component_fusion_gain_lower (l l' : Nat) (hl : 1 ≤ l) (hl' : 1 ≤ l') :
    Nat.fib (min l l' + 1) ≤ Nat.fib (l + 1) * Nat.fib (l' + 1) := by
  rcases Nat.le_total l l' with hll | hll
  · -- min l l' = l
    rw [Nat.min_eq_left hll]
    calc Nat.fib (l + 1)
        = Nat.fib (l + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ Nat.fib (l + 1) * Nat.fib (l' + 1) :=
          Nat.mul_le_mul_left _ (Nat.fib_pos.mpr (by omega))
  · -- min l l' = l'
    rw [Nat.min_eq_right hll]
    calc Nat.fib (l' + 1)
        = 1 * Nat.fib (l' + 1) := (Nat.one_mul _).symm
      _ ≤ Nat.fib (l + 1) * Nat.fib (l' + 1) :=
          Nat.mul_le_mul_right _ (Nat.fib_pos.mpr (by omega))

/-- Combined: the fusion gain F(l+l'+3) - F(l+2)*F(l'+2) is at least F(min(l,l')+1).
    Paper reference: cor:pom-fib-component-fusion-gain (complete form) -/
theorem fib_component_fusion_gain_ge (l l' : Nat) (hl : 1 ≤ l) (hl' : 1 ≤ l') :
    Nat.fib (min l l' + 1) ≤ Nat.fib (l + l' + 3) - Nat.fib (l + 2) * Nat.fib (l' + 2) := by
  rw [fib_component_fusion_gain l l' hl hl']
  exact fib_component_fusion_gain_lower l l' hl hl'

-- ══════════════════════════════════════════════════════════════
-- Phase 235: Splitting refinement gain
-- ══════════════════════════════════════════════════════════════

/-- F(a+2)*F(b+2) < 2*F(a+b+1) for a,b ≥ 2.
    prop:pom-multiplicity-fixed-r-extrema -/
theorem fib_splitting_refinement_gain (a b : Nat) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    Nat.fib (a + 2) * Nat.fib (b + 2) < 2 * Nat.fib (a + b + 1) := by
  -- F(a+b+1) = F(a)*F(b) + F(a+1)*F(b+1)
  have hadd := Nat.fib_add a b
  -- F(a+2) = F(a) + F(a+1), F(b+2) = F(b) + F(b+1)
  have ha2 := Nat.fib_add_two (n := a)
  have hb2 := Nat.fib_add_two (n := b)
  -- Rewrite LHS
  rw [ha2, hb2]
  -- Goal: (F(a)+F(a+1))*(F(b)+F(b+1)) < 2*(F(a)*F(b)+F(a+1)*F(b+1))
  rw [hadd]
  -- Expand LHS using distributivity
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  -- Goal: F(a)*F(b)+F(a)*F(b+1)+F(a+1)*F(b)+F(a+1)*F(b+1) < 2*(F(a)*F(b)+F(a+1)*F(b+1))
  -- i.e. F(a)*F(b+1)+F(a+1)*F(b) < F(a)*F(b)+F(a+1)*F(b+1)
  -- F(b+1) = F(b-1) + F(b)
  have hb_rec := Nat.fib_add_two (n := b - 1)
  rw [show b - 1 + 2 = b + 1 from by omega, show b - 1 + 1 = b from by omega] at hb_rec
  have ha_lt : Nat.fib a < Nat.fib (a + 1) := Nat.fib_lt_fib_succ (by omega)
  have hbm1_pos : 0 < Nat.fib (b - 1) := Nat.fib_pos.mpr (by omega)
  have hkey := Nat.mul_lt_mul_of_pos_right ha_lt hbm1_pos
  -- F(a)*F(b+1) = F(a)*F(b-1) + F(a)*F(b)
  -- F(a+1)*F(b+1) = F(a+1)*F(b-1) + F(a+1)*F(b)
  rw [hb_rec, Nat.mul_add, Nat.mul_add (Nat.fib (a + 1))]
  -- Now goal is linear in the products
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase 236: Fib triple identity + shifted product bounds
-- ══════════════════════════════════════════════════════════════

/-- 3 * F(n+2) = F(n+4) + F(n) for all n.
    aux:pom-fib-triple-identity -/
theorem fib_three_mul (n : Nat) :
    3 * Nat.fib (n + 2) = Nat.fib (n + 4) + Nat.fib n := by
  -- F(n+2) = F(n) + F(n+1)
  have h3 := Nat.fib_add_two (n := n)
  -- F(n+3) = F(n+1) + F(n+2)
  have h2 := Nat.fib_add_two (n := n + 1)
  -- F(n+4) = F(n+2) + F(n+3)
  have h1 := Nat.fib_add_two (n := n + 2)
  -- Normalize: n+2+2 = n+4, n+2+1 = n+3, n+1+2 = n+3, n+1+1 = n+2
  simp only [show n + 2 + 2 = n + 4 from by omega,
             show n + 2 + 1 = n + 3 from by omega,
             show n + 1 + 1 = n + 2 from by omega] at h1 h2
  omega

private theorem fib_shifted_fusion_aux (a b : Nat) :
    Nat.fib (a + 2) * Nat.fib (b + 2) =
      Nat.fib (a + b + 2) + Nat.fib a * Nat.fib b := by
  -- Nat.fib_add (a+1) b: F(a+b+2) = F(a+1)*F(b) + F(a+2)*F(b+1)
  have hadd := Nat.fib_add (a + 1) b
  rw [show a + 1 + b + 1 = a + b + 2 from by omega,
      show a + 1 + 1 = a + 2 from by omega] at hadd
  -- F(b+2) = F(b) + F(b+1), F(a+2) = F(a) + F(a+1)
  have hb := Nat.fib_add_two (n := b)
  have ha := Nat.fib_add_two (n := a)
  -- LHS = F(a+2)*(F(b)+F(b+1)) = F(a+2)*F(b) + F(a+2)*F(b+1)
  rw [hb, Nat.mul_add]
  -- RHS = F(a+1)*F(b) + F(a+2)*F(b+1) + F(a)*F(b)
  --     = (F(a) + F(a+1))*F(b) + F(a+2)*F(b+1)
  --     = F(a+2)*F(b) + F(a+2)*F(b+1)
  rw [hadd, ha]
  ring

private theorem fib_le_two_pow : ∀ m : Nat, Nat.fib (m + 2) ≤ 2 ^ m
  | 0 => by simp
  | 1 => by simp [Nat.fib]
  | m + 2 => by
    have h1 := fib_le_two_pow (m + 1)
    have h2 := fib_le_two_pow m
    have hrec := Nat.fib_add_two (n := m + 2)
    rw [show m + 2 + 2 = m + 4 from by omega,
        show m + 2 + 1 = m + 3 from by omega] at hrec
    calc Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := hrec
      _ ≤ 2 ^ m + 2 ^ (m + 1) := Nat.add_le_add h2 h1
      _ ≤ 2 ^ (m + 1) + 2 ^ (m + 1) :=
          Nat.add_le_add_right (Nat.pow_le_pow_right (by omega) (by omega)) _
      _ = 2 ^ (m + 2) := by ring

/-- For a list of positive naturals, ∏ F(l_i+2) ≥ F(sum+2).
    prop:pom-path-component-multiplicity-refinement-monotone-extrema (lower bound) -/
theorem fib_shifted_prod_lower_bound (ls : List Nat) (hpos : ∀ l ∈ ls, 1 ≤ l) :
    Nat.fib (ls.sum + 2) ≤ (ls.map (fun l => Nat.fib (l + 2))).prod := by
  induction ls with
  | nil => simp
  | cons a tl ih =>
    simp only [List.sum_cons, List.map_cons, List.prod_cons]
    have htl : ∀ l ∈ tl, 1 ≤ l := fun l hl => hpos l (List.mem_cons_of_mem a hl)
    have ih' := ih htl
    have hfuse := fib_shifted_fusion_aux a tl.sum
    calc Nat.fib (a + tl.sum + 2)
        ≤ Nat.fib (a + 2) * Nat.fib (tl.sum + 2) := by omega
      _ ≤ Nat.fib (a + 2) * (tl.map (fun l => Nat.fib (l + 2))).prod :=
          Nat.mul_le_mul_left _ ih'

/-- For a list of positive naturals, ∏ F(l_i+2) ≤ 2^(sum ls).
    prop:pom-path-component-multiplicity-refinement-monotone-extrema (upper bound) -/
theorem fib_shifted_prod_upper_bound (ls : List Nat) (hpos : ∀ l ∈ ls, 1 ≤ l) :
    (ls.map (fun l => Nat.fib (l + 2))).prod ≤ 2 ^ ls.sum := by
  induction ls with
  | nil => simp
  | cons a tl ih =>
    simp only [List.sum_cons, List.map_cons, List.prod_cons]
    have htl : ∀ l ∈ tl, 1 ≤ l := fun l hl => hpos l (List.mem_cons_of_mem a hl)
    have ih' := ih htl
    calc Nat.fib (a + 2) * (tl.map (fun l => Nat.fib (l + 2))).prod
        ≤ 2 ^ a * 2 ^ tl.sum :=
          Nat.mul_le_mul (fib_le_two_pow a) ih'
      _ = 2 ^ (a + tl.sum) := (Nat.pow_add 2 a tl.sum).symm

private theorem fib_lt_two_pow (m : Nat) (hm : 2 ≤ m) : Nat.fib (m + 2) < 2 ^ m := by
  induction m with
  | zero => omega
  | succ n ih =>
    match n, hm with
    | 0, h => omega
    | 1, _ => simp [Nat.fib]
    | n + 2, _ =>
      have h1 := fib_le_two_pow (n + 1)
      have h2 := fib_le_two_pow (n + 2)
      have hrec : Nat.fib (n + 5) = Nat.fib (n + 3) + Nat.fib (n + 4) := by
        have := Nat.fib_add_two (n := n + 3)
        rw [show n + 3 + 2 = n + 5 from by omega, show n + 3 + 1 = n + 4 from by omega] at this
        exact this
      calc Nat.fib (n + 5)
          = Nat.fib (n + 3) + Nat.fib (n + 4) := hrec
        _ ≤ 2 ^ (n + 1) + 2 ^ (n + 2) := Nat.add_le_add h1 h2
        _ < 2 ^ (n + 2) + 2 ^ (n + 2) := by
            have : 2 ^ (n + 1) < 2 ^ (n + 2) := Nat.pow_lt_pow_right (by omega) (by omega)
            omega
        _ = 2 ^ (n + 3) := by ring

private theorem map_fib_prod_pos (ls : List Nat) :
    0 < (ls.map (fun l => Nat.fib (l + 2))).prod := by
  induction ls with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.prod_cons]
    exact Nat.mul_pos (Nat.fib_pos.mpr (by omega)) ih

/-- Lower bound equality iff single component.
    prop:pom-path-component-multiplicity-refinement-monotone-extrema -/
theorem paper_pom_multiplicity_lower_eq_iff (ls : List Nat) (hpos : ∀ l ∈ ls, 1 ≤ l)
    (hne : ls ≠ []) :
    (ls.map (fun l => Nat.fib (l + 2))).prod = Nat.fib (ls.sum + 2) ↔ ls.length = 1 := by
  constructor
  · intro heq
    by_contra hlen
    rcases ls with _ | ⟨a, _ | ⟨b, tl⟩⟩
    · exact absurd rfl hne
    · simp at hlen
    · simp only [List.map_cons, List.prod_cons, List.sum_cons] at heq
      have ha : 1 ≤ a := hpos a (by simp)
      have hb : 1 ≤ b := hpos b (by simp)
      have htl : ∀ l ∈ tl, 1 ≤ l := fun l hl => hpos l (by simp [hl])
      -- Use: prod on b::tl ≥ F(b + tl.sum + 2)
      have hlb2 := fib_shifted_prod_lower_bound (b :: tl)
        (fun l hl => hpos l (by simp [hl]))
      simp only [List.map_cons, List.prod_cons, List.sum_cons] at hlb2
      -- Use: F(a+2)*F(k+2) > F(a+k+2) for k = b+tl.sum ≥ 1
      have hfuse := fib_shifted_fusion_aux a (b + tl.sum)
      have hdefect_pos : 0 < Nat.fib a * Nat.fib (b + tl.sum) :=
        Nat.mul_pos (Nat.fib_pos.mpr (by omega)) (Nat.fib_pos.mpr (by omega))
      -- Chain: F(a+2) * (F(b+2) * tl_prod) ≥ F(a+2) * F(b+tl.sum+2) > F(a+b+tl.sum+2)
      have h1 : Nat.fib (a + (b + tl.sum) + 2) <
          Nat.fib (a + 2) * Nat.fib (b + tl.sum + 2) := by omega
      have h2 : Nat.fib (a + 2) * Nat.fib (b + tl.sum + 2) ≤
          Nat.fib (a + 2) * (Nat.fib (b + 2) *
            (tl.map (fun l => Nat.fib (l + 2))).prod) :=
        Nat.mul_le_mul_left _ hlb2
      have : a + (b + tl.sum) = a + b + tl.sum := by omega
      linarith
  · intro hlen
    rcases ls with _ | ⟨a, tl⟩
    · exact absurd rfl hne
    · simp at hlen; subst hlen; simp

/-- Upper bound equality iff all ones.
    prop:pom-path-component-multiplicity-refinement-monotone-extrema -/
theorem paper_pom_multiplicity_upper_eq_iff (ls : List Nat) (hpos : ∀ l ∈ ls, 1 ≤ l) :
    (ls.map (fun l => Nat.fib (l + 2))).prod = 2 ^ ls.sum ↔ ∀ l ∈ ls, l = 1 := by
  constructor
  · intro heq
    by_contra hall
    push_neg at hall
    obtain ⟨l₀, hl₀_mem, hl₀_ne⟩ := hall
    have hl₀_ge : 2 ≤ l₀ := by have := hpos l₀ hl₀_mem; omega
    have hlt : (ls.map (fun l => Nat.fib (l + 2))).prod < 2 ^ ls.sum := by
      clear heq
      induction ls with
      | nil => simp at hl₀_mem
      | cons hd tl ih =>
        simp only [List.map_cons, List.prod_cons, List.sum_cons]
        have hhd : 1 ≤ hd := hpos hd (by simp)
        have htl : ∀ l ∈ tl, 1 ≤ l := fun l' hl' =>
          hpos l' (List.mem_cons_of_mem _ hl')
        have hub := fib_shifted_prod_upper_bound tl htl
        rcases List.mem_cons.mp hl₀_mem with rfl | hl₀_tl
        · -- hd = l₀, now hd is renamed to l₀
          have hlt_a : Nat.fib (l₀ + 2) < 2 ^ l₀ := fib_lt_two_pow l₀ hl₀_ge
          calc Nat.fib (l₀ + 2) * (tl.map (fun l => Nat.fib (l + 2))).prod
              < 2 ^ l₀ * (tl.map (fun l => Nat.fib (l + 2))).prod :=
                Nat.mul_lt_mul_of_pos_right hlt_a (map_fib_prod_pos tl)
            _ ≤ 2 ^ l₀ * 2 ^ tl.sum := Nat.mul_le_mul_left _ hub
            _ = 2 ^ (l₀ + tl.sum) := (Nat.pow_add 2 l₀ tl.sum).symm
        · have hfa : Nat.fib (hd + 2) ≤ 2 ^ hd := fib_le_two_pow hd
          have ih' := ih htl hl₀_tl
          calc Nat.fib (hd + 2) * (tl.map (fun l => Nat.fib (l + 2))).prod
              ≤ 2 ^ hd * (tl.map (fun l => Nat.fib (l + 2))).prod :=
                Nat.mul_le_mul_right _ hfa
            _ < 2 ^ hd * 2 ^ tl.sum := Nat.mul_lt_mul_of_pos_left ih' (by positivity)
            _ = 2 ^ (hd + tl.sum) := (Nat.pow_add 2 hd tl.sum).symm
    omega
  · intro hall
    induction ls with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      have hhd := hall hd (by simp)
      have htl : ∀ l ∈ tl, l = 1 := fun l hl =>
        hall l (List.mem_cons_of_mem _ hl)
      have hpos_tl : ∀ l ∈ tl, 1 ≤ l := fun l hl =>
        hpos l (List.mem_cons_of_mem _ hl)
      have ih' := ih hpos_tl htl
      subst hhd; rw [ih']; simp [Nat.fib]; ring

-- ══════════════════════════════════════════════════════════════
-- Phase 237: Fib splitting exact + replacement identities
-- ══════════════════════════════════════════════════════════════

/-- 2*F(a+b+1) = F(a+2)*F(b+2) + F(a-1)*F(b-1) for a, b ≥ 1.
    Quantifies the gain from splitting (a,b) → (1, a+b-1).
    prop:pom-multiplicity-fixed-r-extrema (max proof) -/
theorem fib_splitting_exact (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    2 * Nat.fib (a + b + 1) =
    Nat.fib (a + 2) * Nat.fib (b + 2) + Nat.fib (a - 1) * Nat.fib (b - 1) := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hb
  simp only [show 1 + a' - 1 = a' from by omega, show 1 + b' - 1 = b' from by omega,
             show 1 + a' + 2 = a' + 3 from by omega, show 1 + b' + 2 = b' + 3 from by omega,
             show 1 + a' + (1 + b') + 1 = a' + b' + 3 from by omega]
  -- Goal: 2*F(a'+b'+3) = F(a'+3)*F(b'+3) + F(a')*F(b')
  -- fib_shifted_fusion_aux: F(a'+3)*F(b'+3) = F(a'+b'+4) + F(a'+1)*F(b'+1)
  have h1 := fib_shifted_fusion_aux (a' + 1) (b' + 1)
  rw [show a' + 1 + 2 = a' + 3 from by omega, show b' + 1 + 2 = b' + 3 from by omega,
      show a' + 1 + (b' + 1) + 2 = a' + b' + 4 from by omega] at h1
  -- Nat.fib_add a' b': F(a'+b'+1) = F(a')*F(b') + F(a'+1)*F(b'+1)
  have h2 := Nat.fib_add a' b'
  -- F(a'+b'+4) = F(a'+b'+2) + F(a'+b'+3)
  have h3 := Nat.fib_add_two (n := a' + b' + 2)
  rw [show a' + b' + 2 + 2 = a' + b' + 4 from by omega,
      show a' + b' + 2 + 1 = a' + b' + 3 from by omega] at h3
  -- F(a'+b'+3) = F(a'+b'+1) + F(a'+b'+2)
  have h4 := Nat.fib_add_two (n := a' + b' + 1)
  rw [show a' + b' + 1 + 2 = a' + b' + 3 from by omega,
      show a' + b' + 1 + 1 = a' + b' + 2 from by omega] at h4
  nlinarith

/-- 2 * F(n+4) = 3 * F(n+3) + F(n) for all n.
    prop:pom-multiplicity-fixed-r-extrema (min proof, step 1) -/
theorem fib_replace_12_gain (n : Nat) :
    2 * Nat.fib (n + 4) = 3 * Nat.fib (n + 3) + Nat.fib n := by
  have h1 := Nat.fib_add_two (n := n + 2)
  have h2 := Nat.fib_add_two (n := n + 1)
  have h3 := Nat.fib_add_two (n := n)
  simp only [show n + 2 + 2 = n + 4 from by omega,
             show n + 2 + 1 = n + 3 from by omega,
             show n + 1 + 1 = n + 2 from by omega] at h1 h2
  omega

/-- F(a+4)*F(b+4) = 3*F(a+b+4) + F(a)*F(b) for all a, b.
    prop:pom-multiplicity-fixed-r-extrema (min proof, step 2) -/
theorem fib_merge_22_gain (a b : Nat) :
    Nat.fib (a + 4) * Nat.fib (b + 4) = 3 * Nat.fib (a + b + 4) + Nat.fib a * Nat.fib b := by
  have h1 := fib_shifted_fusion_aux (a + 2) (b + 2)
  rw [show a + 2 + 2 = a + 4 from by omega, show b + 2 + 2 = b + 4 from by omega,
      show a + 2 + (b + 2) + 2 = a + b + 6 from by omega] at h1
  have h2 := fib_shifted_fusion_aux a b
  have h3 := fib_three_mul (a + b + 2)
  rw [show a + b + 2 + 2 = a + b + 4 from by omega,
      show a + b + 2 + 4 = a + b + 6 from by omega] at h3
  omega

end Omega
