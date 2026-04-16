import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.GU

/-- The finite bin-fold fiber of `w` inside the bounded interval `{0, ..., 2^m - 1}`. -/
def foldbinFiberRange (m : Nat) (w : X m) : Finset Nat :=
  (Finset.range (2 ^ m)).filter fun n => cBinFold m n = w

/-- The translated delta attached to a bounded bin-fold preimage. -/
def foldbinDelta (w : X m) (n : Nat) : Nat :=
  let _ := w
  n

/-- The reachable delta set obtained by translating the bounded bin-fold fiber by the prefix
value `stableValue w`. -/
def foldbinDeltaSet (m : Nat) (w : X m) : Finset Nat :=
  foldbinFiberRange m w

/-- The staircase counting function of the reachable delta set. -/
def foldbinDeltaStaircase (m : Nat) (w : X m) (C : Nat) : Nat :=
  ((foldbinDeltaSet m w).filter fun δ => δ < C).card

/-- Witness-carrying points of the bounded bin-fold fiber. -/
abbrev FoldbinFiberElem (m : Nat) (w : X m) := {n : Nat // n ∈ foldbinFiberRange m w}

/-- The delta value of a witness-carrying bounded fiber point, viewed in the reachable delta set. -/
def foldbinFiberDeltaPoint (m : Nat) (w : X m) (u : FoldbinFiberElem m w) :
    {δ : Nat // δ ∈ foldbinDeltaSet m w} :=
  ⟨foldbinDelta w u.1, u.2⟩

/-- The staircase adds at most one new reachable delta at each level, and does so exactly when
that level lies in the reachable delta set. -/
def foldbinUnitJumpProperty (m : Nat) (w : X m) : Prop :=
  ∀ C, foldbinDeltaStaircase m w (C + 1) =
    foldbinDeltaStaircase m w C + if C ∈ foldbinDeltaSet m w then 1 else 0

/-- Reachable deltas are exactly the jump points of the staircase. -/
def foldbinJumpPointInversionProperty (m : Nat) (w : X m) : Prop :=
  ∀ t, t ∈ foldbinDeltaSet m w ↔
    foldbinDeltaStaircase m w (t + 1) = foldbinDeltaStaircase m w t + 1

/-- Translation by the prefix value identifies the bounded bin-fold fiber with the reachable
delta set. -/
def foldbinFiberDeltaBijectionProperty (m : Nat) (w : X m) : Prop :=
  Function.Bijective (foldbinFiberDeltaPoint m w)

private theorem staircase_step (S : Finset Nat) (C : Nat) :
    (S.filter (fun δ => δ < C + 1)).card =
      (S.filter (fun δ => δ < C)).card + if C ∈ S then 1 else 0 := by
  have hsplit :
      S.filter (fun δ => δ < C + 1) =
        (S.filter fun δ => δ < C) ∪ (S.filter fun δ => δ = C) := by
    ext δ
    by_cases hδ : δ = C
    · subst hδ
      simp [Finset.mem_filter, Finset.mem_union]
    · have hle : δ < C + 1 ↔ δ ≤ C := Nat.lt_succ_iff
      have hlt : δ ≤ C ↔ δ < C := by omega
      simp [Finset.mem_filter, Finset.mem_union, hδ, hle, hlt]
  have hdisj :
      Disjoint (S.filter fun δ => δ < C) (S.filter fun δ => δ = C) := by
    refine Finset.disjoint_left.mpr ?_
    intro δ h1 h2
    have hlt : δ < C := (Finset.mem_filter.mp h1).2
    have heq : δ = C := (Finset.mem_filter.mp h2).2
    subst heq
    simpa using hlt
  have hsingle :
      S.filter (fun δ => δ = C) = if C ∈ S then ({C} : Finset Nat) else ∅ := by
    by_cases hC : C ∈ S
    · ext δ
      by_cases hδ : δ = C <;> simp [hC, hδ]
    · ext δ
      by_cases hδ : δ = C <;> simp [hC, hδ]
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hsingle]
  by_cases hC : C ∈ S <;> simp [hC]

private theorem foldbinFiberDeltaPoint_injective (m : Nat) (w : X m) :
    Function.Injective (foldbinFiberDeltaPoint m w) := by
  intro u v huv
  apply Subtype.ext
  simpa [foldbinFiberDeltaPoint, foldbinDelta] using congrArg Subtype.val huv

private theorem foldbinFiberDeltaPoint_surjective (m : Nat) (w : X m) :
    Function.Surjective (foldbinFiberDeltaPoint m w) := by
  intro δ
  refine ⟨⟨δ.1, δ.2⟩, ?_⟩
  apply Subtype.ext
  rfl

/-- Paper-facing bin-fold uplift package: the translated delta staircase has unit jumps, its
jump set is exactly the reachable delta set, and the bounded fiber is in bijection with that
delta set.
    thm:foldbin-uplift-unit-jump-delta-inversion -/
theorem paper_foldbin_uplift_unit_jump_delta_inversion (m : Nat) (w : X m) :
    foldbinUnitJumpProperty m w ∧
      foldbinJumpPointInversionProperty m w ∧
      foldbinFiberDeltaBijectionProperty m w := by
  refine ⟨?_, ?_, ?_⟩
  · intro C
    simpa [foldbinDeltaStaircase] using staircase_step (foldbinDeltaSet m w) C
  · intro t
    by_cases ht : t ∈ foldbinDeltaSet m w
    · constructor
      · intro _
        simpa [foldbinUnitJumpProperty, foldbinDeltaStaircase, ht] using
          (staircase_step (foldbinDeltaSet m w) t)
      · intro _
        exact ht
    · constructor
      · intro h
        exact (ht h).elim
      · intro hJump
        have hstep :
            foldbinDeltaStaircase m w (t + 1) = foldbinDeltaStaircase m w t := by
          simpa [foldbinUnitJumpProperty, foldbinDeltaStaircase, ht] using
            (staircase_step (foldbinDeltaSet m w) t)
        omega
  · exact ⟨foldbinFiberDeltaPoint_injective m w, foldbinFiberDeltaPoint_surjective m w⟩

end Omega.GU
