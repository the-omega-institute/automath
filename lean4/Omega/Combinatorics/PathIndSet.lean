import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Fin.Basic
import Omega.Core.Fib

/-! # Path-graph independent sets and Fibonacci numbers

We prove that the number of independent sets (no two adjacent elements)
on the path graph P_n equals the Fibonacci number F(n+2).
-/

namespace Omega

/-- An independent set on the path graph P_n: a subset of Fin n
    with no two adjacent elements.
    infra:path-ind-set-def -/
def IsPathIndependent (n : Nat) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ¬ (i.val + 1 = j.val)

instance pathIndDecidable (n : Nat) (S : Finset (Fin n)) :
    Decidable (IsPathIndependent n S) := by
  unfold IsPathIndependent; exact inferInstance

/-- The count of independent sets on P_n.
    infra:path-ind-count-def -/
def pathIndCount (n : Nat) : Nat :=
  (Finset.univ.filter (fun S : Finset (Fin n) =>
    IsPathIndependent n S)).card

-- ══════════════════════════════════════════════════════════════
-- Partition of Fin(n+2) independent sets by last element membership
-- ══════════════════════════════════════════════════════════════

private def notContainingLast (n : Nat) :=
  Finset.univ.filter (fun S : Finset (Fin (n + 2)) =>
    IsPathIndependent (n + 2) S ∧ Fin.last (n + 1) ∉ S)

private def containingLast (n : Nat) :=
  Finset.univ.filter (fun S : Finset (Fin (n + 2)) =>
    IsPathIndependent (n + 2) S ∧ Fin.last (n + 1) ∈ S)

theorem pathInd_partition (n : Nat) :
    Finset.univ.filter (fun S : Finset (Fin (n + 2)) =>
      IsPathIndependent (n + 2) S) =
    notContainingLast n ∪ containingLast n := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    notContainingLast, containingLast]
  constructor
  · intro h
    by_cases hm : Fin.last (n + 1) ∈ S
    · right; exact ⟨h, hm⟩
    · left; exact ⟨h, hm⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

theorem pathInd_disjoint (n : Nat) :
    Disjoint (notContainingLast n) (containingLast n) := by
  simp only [notContainingLast, containingLast]
  rw [Finset.disjoint_filter]
  intro S _ ⟨_, h1⟩ ⟨_, h2⟩
  exact h1 h2

-- ══════════════════════════════════════════════════════════════
-- Bijection: not containing last ↔ independent sets of Fin(n+1)
-- ══════════════════════════════════════════════════════════════

def liftIndSet (n : Nat) (S : Finset (Fin (n + 1))) : Finset (Fin (n + 2)) :=
  S.map Fin.castSuccEmb

theorem liftIndSet_indep {n : Nat} {S : Finset (Fin (n + 1))}
    (hS : IsPathIndependent (n + 1) S) :
    IsPathIndependent (n + 2) (liftIndSet n S) := by
  intro i hi j hj hadj
  simp only [liftIndSet, Finset.mem_map] at hi hj
  obtain ⟨a, ha, rfl⟩ := hi
  obtain ⟨b, hb, rfl⟩ := hj
  exact hS a ha b hb hadj

theorem liftIndSet_not_last {n : Nat} (S : Finset (Fin (n + 1))) :
    Fin.last (n + 1) ∉ liftIndSet n S := by
  simp only [liftIndSet, Finset.mem_map]
  intro ⟨a, _, h⟩
  have := congrArg Fin.val h
  simp [Fin.last] at this
  omega

theorem liftIndSet_injective (n : Nat) :
    Function.Injective (liftIndSet n) :=
  fun _ _ h => Finset.map_injective _ h

theorem liftIndSet_mem_notContainingLast {n : Nat} {S : Finset (Fin (n + 1))}
    (hS : IsPathIndependent (n + 1) S) :
    liftIndSet n S ∈ notContainingLast n := by
  simp only [notContainingLast, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨liftIndSet_indep hS, liftIndSet_not_last S⟩

private theorem castSucc_injOn_preimage {n : Nat} (s : Finset (Fin (n + 2))) :
    Set.InjOn (Fin.castSucc (n := n + 1)) ((Fin.castSucc (n := n + 1)) ⁻¹' (↑s : Set (Fin (n + 2)))) :=
  fun _ _ _ _ h => Fin.castSucc_injective _ h

theorem mem_notContainingLast_iff_lift {n : Nat} (T : Finset (Fin (n + 2))) :
    T ∈ notContainingLast n ↔
    ∃ S : Finset (Fin (n + 1)), IsPathIndependent (n + 1) S ∧ liftIndSet n S = T := by
  constructor
  · intro hT
    simp only [notContainingLast, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    obtain ⟨hInd, hLast⟩ := hT
    refine ⟨T.preimage Fin.castSucc (castSucc_injOn_preimage T), ?_, ?_⟩
    · intro i hi j hj hadj
      rw [Finset.mem_preimage] at hi hj
      exact hInd (Fin.castSucc i) hi (Fin.castSucc j) hj hadj
    · ext x
      constructor
      · -- x ∈ liftIndSet n (preimage) → x ∈ T
        intro hx
        rw [liftIndSet, Finset.mem_map] at hx
        obtain ⟨a, ha, hax⟩ := hx
        rw [Finset.mem_preimage] at ha
        rw [← hax]; exact ha
      · -- x ∈ T → x ∈ liftIndSet n (preimage)
        intro hx
        rw [liftIndSet, Finset.mem_map]
        have hxlt : x.val < n + 1 := by
          by_contra hge
          push_neg at hge
          have hle : x.val ≤ n + 1 := Nat.lt_succ_iff.mp x.isLt
          have hxeq : x = Fin.last (n + 1) := by ext; simp [Fin.last]; omega
          exact hLast (hxeq ▸ hx)
        refine ⟨⟨x.val, hxlt⟩, ?_, ?_⟩
        · rw [Finset.mem_preimage]; exact hx
        · ext; simp [Fin.castSuccEmb]
  · intro ⟨S, hS, hST⟩
    rw [← hST]
    exact liftIndSet_mem_notContainingLast hS

theorem card_notContainingLast (n : Nat) :
    (notContainingLast n).card = pathIndCount (n + 1) := by
  have heq : notContainingLast n =
    (Finset.univ.filter (fun S : Finset (Fin (n + 1)) =>
      IsPathIndependent (n + 1) S)).image (liftIndSet n) := by
    ext T
    constructor
    · intro hT
      rw [mem_notContainingLast_iff_lift] at hT
      obtain ⟨S, hS, rfl⟩ := hT
      exact Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩, rfl⟩
    · intro hT
      rw [Finset.mem_image] at hT
      obtain ⟨S, hS, rfl⟩ := hT
      exact liftIndSet_mem_notContainingLast (Finset.mem_filter.mp hS).2
  rw [heq, Finset.card_image_of_injective _ (liftIndSet_injective n)]
  rfl

-- ══════════════════════════════════════════════════════════════
-- Bijection: containing last ↔ independent sets of Fin(n)
-- ══════════════════════════════════════════════════════════════

private def castSuccSuccEmb (n : Nat) : Fin n ↪ Fin (n + 2) :=
  (Fin.castSuccEmb (n := n)).trans (Fin.castSuccEmb (n := n + 1))

private theorem castSuccSucc_val {n : Nat} (a : Fin n) :
    (castSuccSuccEmb n a).val = a.val := by
  simp [castSuccSuccEmb, Function.Embedding.trans, Fin.castSuccEmb]

private theorem castSuccSucc_ne_last {n : Nat} (a : Fin n) :
    castSuccSuccEmb n a ≠ Fin.last (n + 1) := by
  intro h
  have := congrArg Fin.val h
  rw [castSuccSucc_val] at this
  simp [Fin.last] at this
  omega

private theorem castSuccSuccEmb_injOn {n : Nat} (s : Finset (Fin (n + 2))) :
    Set.InjOn (castSuccSuccEmb n) ((castSuccSuccEmb n) ⁻¹' ↑s) :=
  fun _ _ _ _ h => (castSuccSuccEmb n).injective h

def liftWithLast (n : Nat) (S : Finset (Fin n)) : Finset (Fin (n + 2)) :=
  insert (Fin.last (n + 1)) (S.map (castSuccSuccEmb n))

theorem liftWithLast_indep {n : Nat} {S : Finset (Fin n)}
    (hS : IsPathIndependent n S) :
    IsPathIndependent (n + 2) (liftWithLast n S) := by
  intro i hi j hj hadj
  simp only [liftWithLast, Finset.mem_insert, Finset.mem_map] at hi hj
  rcases hi with rfl | ⟨a, ha, rfl⟩ <;> rcases hj with rfl | ⟨b, hb, rfl⟩
  · simp [Fin.last] at hadj
  · simp [Fin.last, castSuccSucc_val] at hadj; omega
  · simp [Fin.last, castSuccSucc_val] at hadj; have := a.isLt; omega
  · rw [castSuccSucc_val, castSuccSucc_val] at hadj
    exact hS a ha b hb hadj

theorem liftWithLast_has_last (n : Nat) (S : Finset (Fin n)) :
    Fin.last (n + 1) ∈ liftWithLast n S := by
  simp [liftWithLast]

private theorem last_not_mem_map_castSuccSucc {n : Nat} (S : Finset (Fin n)) :
    Fin.last (n + 1) ∉ S.map (castSuccSuccEmb n) := by
  simp only [Finset.mem_map]
  intro ⟨a, _, h⟩
  exact castSuccSucc_ne_last a (h.symm ▸ rfl)

theorem liftWithLast_injective (n : Nat) :
    Function.Injective (liftWithLast n : Finset (Fin n) → Finset (Fin (n + 2))) := by
  intro S T hST
  simp only [liftWithLast] at hST
  have hS_nmem := last_not_mem_map_castSuccSucc S
  have hT_nmem := last_not_mem_map_castSuccSucc T
  have : S.map (castSuccSuccEmb n) = T.map (castSuccSuccEmb n) := by
    ext x
    by_cases hx : x = Fin.last (n + 1)
    · subst hx; constructor <;> intro h <;> [exact absurd h hS_nmem; exact absurd h hT_nmem]
    · constructor <;> intro hm
      · have h1 : x ∈ insert (Fin.last (n + 1)) (S.map (castSuccSuccEmb n)) :=
          Finset.mem_insert.mpr (Or.inr hm)
        rw [hST] at h1
        exact (Finset.mem_insert.mp h1).resolve_left hx
      · have h1 : x ∈ insert (Fin.last (n + 1)) (T.map (castSuccSuccEmb n)) :=
          Finset.mem_insert.mpr (Or.inr hm)
        rw [← hST] at h1
        exact (Finset.mem_insert.mp h1).resolve_left hx
  exact Finset.map_injective _ this

theorem mem_containingLast_iff_liftWithLast {n : Nat} (T : Finset (Fin (n + 2))) :
    T ∈ containingLast n ↔
    ∃ S : Finset (Fin n), IsPathIndependent n S ∧ liftWithLast n S = T := by
  constructor
  · intro hT
    simp only [containingLast, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    obtain ⟨hInd, hLast⟩ := hT
    have hPen : (⟨n, by omega⟩ : Fin (n + 2)) ∉ T := by
      intro hpen
      exact hInd ⟨n, by omega⟩ hpen (Fin.last (n + 1)) hLast (by simp [Fin.last])
    let T' := T.erase (Fin.last (n + 1))
    have hT'sub : ∀ x ∈ T', x.val < n := by
      intro x hx
      rw [Finset.mem_erase] at hx
      obtain ⟨hne, hxT⟩ := hx
      have hxne : x.val ≠ n + 1 := by
        intro h; exact hne (by ext; simp [Fin.last]; exact h)
      have hxnpen : x.val ≠ n := by
        intro h
        exact hPen (show (⟨n, by omega⟩ : Fin (n + 2)) ∈ T from by
          convert hxT using 1; ext; exact h.symm)
      omega
    refine ⟨T'.preimage (castSuccSuccEmb n) (castSuccSuccEmb_injOn T'), ?_, ?_⟩
    · intro i hi j hj hadj
      rw [Finset.mem_preimage] at hi hj
      have hiT : (castSuccSuccEmb n i) ∈ T := (Finset.mem_erase.mp hi).2
      have hjT : (castSuccSuccEmb n j) ∈ T := (Finset.mem_erase.mp hj).2
      exact hInd _ hiT _ hjT (by rw [castSuccSucc_val, castSuccSucc_val]; exact hadj)
    · -- Show: liftWithLast of the preimage equals T
      ext x
      constructor
      · -- x ∈ liftWithLast (...) → x ∈ T
        intro hx
        rw [liftWithLast, Finset.mem_insert, Finset.mem_map] at hx
        rcases hx with rfl | ⟨a, ha, rfl⟩
        · exact hLast
        · rw [Finset.mem_preimage] at ha
          exact (Finset.mem_erase.mp ha).2
      · -- x ∈ T → x ∈ liftWithLast (...)
        intro hx
        rw [liftWithLast, Finset.mem_insert, Finset.mem_map]
        by_cases hxlast : x = Fin.last (n + 1)
        · left; exact hxlast
        · right
          have hxlt : x.val < n := by
            have hxne : x.val ≠ n + 1 := by
              intro h; exact hxlast (by ext; simp [Fin.last]; exact h)
            have hxnpen : x.val ≠ n := by
              intro h; exact hPen (show (⟨n, by omega⟩ : Fin (n + 2)) ∈ T from by
                convert hx using 1; ext; exact h.symm)
            omega
          refine ⟨⟨x.val, hxlt⟩, ?_, ?_⟩
          · rw [Finset.mem_preimage, Finset.mem_erase]
            refine ⟨castSuccSucc_ne_last ⟨x.val, hxlt⟩, ?_⟩
            have : castSuccSuccEmb n ⟨x.val, hxlt⟩ = x := by
              ext; exact (castSuccSucc_val ⟨x.val, hxlt⟩).symm
            rw [this]; exact hx
          · ext; exact (castSuccSucc_val ⟨x.val, hxlt⟩).symm
  · intro ⟨S, hS, hST⟩
    simp only [containingLast, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hST]
    exact ⟨liftWithLast_indep hS, liftWithLast_has_last n S⟩

theorem card_containingLast (n : Nat) :
    (containingLast n).card = pathIndCount n := by
  have heq : containingLast n =
    (Finset.univ.filter (fun S : Finset (Fin n) =>
      IsPathIndependent n S)).image (liftWithLast n) := by
    ext T
    constructor
    · intro hT
      rw [mem_containingLast_iff_liftWithLast] at hT
      obtain ⟨S, hS, rfl⟩ := hT
      exact Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩, rfl⟩
    · intro hT
      rw [Finset.mem_image] at hT
      obtain ⟨S, hS, rfl⟩ := hT
      rw [mem_containingLast_iff_liftWithLast]
      exact ⟨S, (Finset.mem_filter.mp hS).2, rfl⟩
  rw [heq, Finset.card_image_of_injective _ (liftWithLast_injective n)]
  rfl

-- ══════════════════════════════════════════════════════════════
-- The Fibonacci recurrence for pathIndCount
-- ══════════════════════════════════════════════════════════════

/-- infra:path-ind-count-recurrence -/
theorem pathIndCount_recurrence (n : Nat) :
    pathIndCount (n + 2) = pathIndCount (n + 1) + pathIndCount n := by
  show (Finset.univ.filter (fun S : Finset (Fin (n + 2)) =>
    IsPathIndependent (n + 2) S)).card = pathIndCount (n + 1) + pathIndCount n
  conv_lhs => rw [pathInd_partition n]
  rw [Finset.card_union_of_disjoint (pathInd_disjoint n),
    card_notContainingLast n, card_containingLast n]

-- ══════════════════════════════════════════════════════════════
-- Base cases
-- ══════════════════════════════════════════════════════════════

theorem pathIndCount_zero : pathIndCount 0 = 1 := by
  simp [pathIndCount, IsPathIndependent]

theorem pathIndCount_one : pathIndCount 1 = 2 := by decide

-- ══════════════════════════════════════════════════════════════
-- Main theorem
-- ══════════════════════════════════════════════════════════════

/-- The number of independent sets of the path graph P_n equals F(n+2).
    infra:path-ind-set-count -/
theorem path_independent_set_count (n : Nat) :
    pathIndCount n = Nat.fib (n + 2) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => exact pathIndCount_zero
    | 1 => exact pathIndCount_one
    | n + 2 =>
      rw [pathIndCount_recurrence, ih (n + 1) (by omega), ih n (by omega)]
      exact (fib_succ_succ' (n + 2)).symm

/-- The number of independent sets of the path graph P_n equals F(n+2).
    (Statement using Finset.filter directly.)
    infra:path-ind-set-count-filter -/
theorem path_independent_set_count' (n : Nat) :
    (Finset.univ.filter (fun S : Finset (Fin n) => IsPathIndependent n S)).card
    = Nat.fib (n + 2) :=
  path_independent_set_count n

-- ══════════════════════════════════════════════════════════════
-- Phase 208: Strict monotonicity
-- ══════════════════════════════════════════════════════════════

/-- Path independent set count is strictly increasing for n >= 2.
    prop:folding-stable-syntax-fibonacci-count -/
theorem pathIndCount_strict_mono (n : Nat) (hn : 2 ≤ n) :
    pathIndCount n < pathIndCount (n + 1) := by
  rw [path_independent_set_count, path_independent_set_count]
  exact fib_strict_mono (n + 2) (by omega)

-- ══════════════════════════════════════════════════════════════
-- Phase 212: Path independent set size upper bound
-- ══════════════════════════════════════════════════════════════

/-- The halving map i ↦ i/2 is injective on path-independent sets. -/
private theorem half_injOn_pathInd (n : Nat) (S : Finset (Fin n))
    (hS : IsPathIndependent n S) :
    Set.InjOn (fun i : Fin n => i.val / 2) (↑S) := by
  intro i hi j hj (heq : i.val / 2 = j.val / 2)
  ext
  by_contra hne
  -- WLOG i.val < j.val
  have hne_val : i.val ≠ j.val := hne
  rcases Nat.lt_or_gt_of_ne hne_val with hlt | hlt
  · have hnotadj : ¬ (i.val + 1 = j.val) := hS i hi j hj
    have hge2 : i.val + 2 ≤ j.val := by omega
    have : (i.val + 2) / 2 ≤ j.val / 2 := Nat.div_le_div_right hge2
    have : i.val / 2 + 1 ≤ j.val / 2 := by
      calc i.val / 2 + 1 = (i.val + 2) / 2 := by omega
        _ ≤ j.val / 2 := this
    omega
  · have hnotadj : ¬ (j.val + 1 = i.val) := hS j hj i hi
    have hge2 : j.val + 2 ≤ i.val := by omega
    have : (j.val + 2) / 2 ≤ i.val / 2 := Nat.div_le_div_right hge2
    have : j.val / 2 + 1 ≤ i.val / 2 := by
      calc j.val / 2 + 1 = (j.val + 2) / 2 := by omega
        _ ≤ i.val / 2 := this
    omega

/-- Any path-independent set on P_n has at most ⌈n/2⌉ elements.
    thm:pom-fibcube-eccentricity-closed-form -/
theorem pathIndSet_card_le (n : Nat) (S : Finset (Fin n))
    (hS : IsPathIndependent n S) :
    S.card ≤ (n + 1) / 2 := by
  have hInj := half_injOn_pathInd n S hS
  have hImage : S.image (fun i : Fin n => i.val / 2) ⊆ Finset.range ((n + 1) / 2) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    simp only [Finset.mem_range]
    exact Nat.div_lt_of_lt_mul (by omega)
  calc S.card
      = (S.image (fun i : Fin n => i.val / 2)).card :=
          (Finset.card_image_of_injOn hInj).symm
      _ ≤ (Finset.range ((n + 1) / 2)).card := Finset.card_le_card hImage
      _ = (n + 1) / 2 := Finset.card_range _

-- ══════════════════════════════════════════════════════════════
-- Phase 229: maximum path-independent set achievability
-- ══════════════════════════════════════════════════════════════

/-- Maximum path-independent set achievability: exists S with card = ceil(n/2).
    thm:pom-fibcube-eccentricity-closed-form -/
theorem pathIndSet_exists_max (n : Nat) (_hn : 1 ≤ n) :
    ∃ S : Finset (Fin n), IsPathIndependent n S ∧ S.card = (n + 1) / 2 := by
  -- Construct the even-index set {i : Fin n | i.val % 2 = 0}
  refine ⟨Finset.univ.filter (fun i : Fin n => i.val % 2 = 0), ?_, ?_⟩
  · -- IsPathIndependent: no two elements are adjacent
    intro i hi j hj hadj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    -- i.val is even, j.val = i.val + 1 is odd
    omega
  · -- Card = (n+1)/2: count of even positions in Fin n
    -- Biject with Fin ((n+1)/2) via k ↦ 2*k
    rw [show (n + 1) / 2 = Fintype.card (Fin ((n + 1) / 2)) from by simp,
      ← Finset.card_univ (α := Fin ((n + 1) / 2))]
    symm
    have hdiv : (n + 1) / 2 * 2 ≤ n + 1 := Nat.div_mul_le_self (n + 1) 2
    have hbound : ∀ k, k < (n + 1) / 2 → 2 * k < n := by intro k hk; omega
    apply Finset.card_nbij (fun (k : Fin ((n + 1) / 2)) =>
      (⟨2 * k.val, hbound k.val k.isLt⟩ : Fin n))
    · intro ⟨k, hk⟩ _
      show (⟨2 * k, _⟩ : Fin n) ∈ Finset.univ.filter (fun i : Fin n => i.val % 2 = 0)
      simp [Finset.mem_filter, Nat.mul_mod_right]
    · intro ⟨k₁, _⟩ _ ⟨k₂, _⟩ _ h
      have h1 := congrArg Fin.val h; simp at h1
      exact Fin.ext (by linarith)
    · intro ⟨i, hi⟩ hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hx
      have hlt : i / 2 < (n + 1) / 2 := by omega
      exact ⟨⟨i / 2, hlt⟩, Finset.mem_coe.mpr (Finset.mem_univ _),
        Fin.ext (by simp only []; omega)⟩

-- ══════════════════════════════════════════════════════════════
-- Phase 230: Cassini identity for pathIndCount
-- ══════════════════════════════════════════════════════════════

/-- Cassini identity for path independent set counts.
    thm:pom-path-indset-thermo-constants -/
theorem pathIndCount_cassini (n : Nat) :
    pathIndCount (n + 2) * pathIndCount n + (n + 1) % 2 =
    pathIndCount (n + 1) ^ 2 + n % 2 := by
  simp only [path_independent_set_count]
  -- Goal: F(n+4)*F(n+2) + (n+1)%2 = F(n+3)^2 + n%2
  by_cases heven : Even n
  · -- Even n: (n+1)%2 = 1, n%2 = 0
    have h1 : (n + 1) % 2 = 1 := by rcases heven with ⟨k, rfl⟩; omega
    have h0 : n % 2 = 0 := by rcases heven with ⟨k, rfl⟩; omega
    rw [h1, h0, Nat.add_zero]
    -- F(n+2) is even, so fib_cassini_even at (n+2): F(n+2)*F(n+4) + 1 = F(n+3)^2
    have heven2 : Even (n + 2) := by rcases heven with ⟨k, rfl⟩; exact ⟨k + 1, by omega⟩
    have := fib_cassini_even (n + 2) heven2
    linarith [Nat.mul_comm (Nat.fib (n + 2)) (Nat.fib (n + 4))]
  · -- Odd n: (n+1)%2 = 0, n%2 = 1
    have hmod : n % 2 = 1 := by
      rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact absurd ⟨k, rfl⟩ heven
      · omega
    have h0 : (n + 1) % 2 = 0 := by omega
    rw [h0, hmod, Nat.add_zero]
    -- F(n+2) is odd, so fib_cassini_odd at (n+2): F(n+2)*F(n+4) = F(n+3)^2 + 1
    have hodd2 : ¬ Even (n + 2) := by intro ⟨k, hk⟩; exact heven ⟨k - 1, by omega⟩
    have := fib_cassini_odd (n + 2) hodd2
    linarith [Nat.mul_comm (Nat.fib (n + 2)) (Nat.fib (n + 4))]

/-- pathIndCount 2 = 3.
    infra:path-ind-set-count -/
theorem pathIndCount_two : pathIndCount 2 = 3 := by
  rw [path_independent_set_count]; native_decide

/-- pathIndCount 3 = 5.
    infra:path-ind-set-count -/
theorem pathIndCount_three : pathIndCount 3 = 5 := by
  rw [path_independent_set_count]; native_decide

/-- pathIndCount 4 = 8.
    infra:path-ind-set-count -/
theorem pathIndCount_four : pathIndCount 4 = 8 := by
  rw [path_independent_set_count]; native_decide

/-- pathIndCount 5 = 13.
    infra:path-ind-set-count -/
theorem pathIndCount_five : pathIndCount 5 = 13 := by
  rw [path_independent_set_count]; native_decide

/-- Paper small-value package for pathIndCount, n = 0..5, plus the F_7 identity.
    prop:folding-stable-syntax-fibonacci-count -/
theorem paper_pathIndCount_small_values_package :
    pathIndCount 0 = 1 ∧
    pathIndCount 1 = 2 ∧
    pathIndCount 2 = 3 ∧
    pathIndCount 3 = 5 ∧
    pathIndCount 4 = 8 ∧
    pathIndCount 5 = 13 ∧
    pathIndCount 5 = Nat.fib 7 :=
  ⟨pathIndCount_zero, pathIndCount_one, pathIndCount_two,
   pathIndCount_three, pathIndCount_four, pathIndCount_five,
   path_independent_set_count 5⟩

end Omega
