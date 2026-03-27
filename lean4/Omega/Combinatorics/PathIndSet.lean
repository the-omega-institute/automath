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

end Omega
